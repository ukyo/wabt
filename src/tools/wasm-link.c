/*
 * Copyright 2016 WebAssembly Community Group participants
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "allocator.h"
#include "binary-reader.h"
#include "binary-writer.h"
#include "option-parser.h"
#include "stream.h"
#include "vector.h"
#include "writer.h"

#define PROGRAM_NAME "wasm-link"
#define NOPE WASM_OPTION_NO_ARGUMENT
#define YEP WASM_OPTION_HAS_ARGUMENT

enum {
  FLAG_VERBOSE,
  FLAG_OUTPUT,
  FLAG_HELP,
  NUM_FLAGS
};

static const char s_description[] =
    "  link one or more wasm binary modules into a single binary module."
    "\n"
    "  $ wasm-link m1.wasm m2.wasm -o out.wasm\n";

static WasmOption s_options[] = {
    {FLAG_VERBOSE, 'v', "verbose", NULL, NOPE,
     "use multiple times for more info"},
    {FLAG_OUTPUT, 'o', "output", "FILE", YEP,
     "output wasm binary file"},
    {FLAG_HELP, 'h', "help", NULL, NOPE, "print this help message"},
};
WASM_STATIC_ASSERT(NUM_FLAGS == WASM_ARRAY_SIZE(s_options));


typedef const char* String;
WASM_DEFINE_VECTOR(filename, String);

static WasmBool s_verbose;
static const char* s_outfile = "a.wasm";
static StringVector s_infiles;
static WasmAllocator* s_allocator;
static WasmFileWriter s_log_stream_writer;
static WasmStream s_log_stream;

static void on_option(struct WasmOptionParser* parser,
                      struct WasmOption* option,
                      const char* argument) {
  switch (option->id) {
    case FLAG_VERBOSE:
      s_verbose++;
      wasm_init_file_writer_existing(&s_log_stream_writer, stdout);
      wasm_init_stream(&s_log_stream, &s_log_stream_writer.base, NULL);
      break;

    case FLAG_OUTPUT:
      s_outfile = argument;
      break;

    case FLAG_HELP:
      wasm_print_help(parser, PROGRAM_NAME);
      exit(0);
      break;
  }
}

static void on_argument(struct WasmOptionParser* parser, const char* argument) {
  *wasm_append_filename(s_allocator, &s_infiles) = argument;
}

static void on_option_error(struct WasmOptionParser* parser,
                            const char* message) {
  WASM_FATAL("%s\n", message);
}

static void parse_options(int argc, char** argv) {
  WasmOptionParser parser;
  WASM_ZERO_MEMORY(parser);
  parser.description = s_description;
  parser.options = s_options;
  parser.num_options = WASM_ARRAY_SIZE(s_options);
  parser.on_option = on_option;
  parser.on_argument = on_argument;
  parser.on_error = on_option_error;
  wasm_parse_options(&parser, argc, argv);

  if (!s_infiles.size) {
    wasm_print_help(&parser, PROGRAM_NAME);
    WASM_FATAL("No inputs files specified.\n");
  }
}

typedef struct Reloc {
  WasmReloc type;
  uint32_t offset;
} Reloc;
WASM_DEFINE_VECTOR(reloc, Reloc);

struct InputBinary;

typedef struct Section {
  WasmBinarySection type;
  uint32_t size;
  uint32_t offset;
  uint32_t count;
  struct InputBinary* binary;
} Section;
WASM_DEFINE_VECTOR(section, Section);

typedef Section* SectionPtr;
WASM_DEFINE_VECTOR(section_ptr, SectionPtr);

typedef struct InputBinary {
  uint8_t* data;
  size_t size;
  SectionVector sections;
  RelocVector relocations;
  uint32_t type_index_offset;
  uint32_t function_index_offset;
  uint32_t global_index_offset;
} InputBinary;
WASM_DEFINE_VECTOR(binary, InputBinary);

static WasmResult on_reloc(WasmReloc type, uint32_t offset, void* user_data) {
  InputBinary* binary = user_data;
  Reloc* reloc = wasm_append_reloc(s_allocator, &binary->relocations);
  reloc->type = type;
  reloc->offset = offset;
  return WASM_OK;
}

static WasmResult begin_section(WasmBinaryReaderContext* ctx,
                                WasmBinarySection section_type,
                                uint32_t size) {
  InputBinary* binary = ctx->user_data;
  Section* sec = wasm_append_section(s_allocator, &binary->sections);
  sec->type = section_type;
  sec->size = size;
  sec->offset = ctx->offset;
  sec->binary = binary;

  if (sec->type != WASM_BINARY_SECTION_USER &&
      sec->type != WASM_BINARY_SECTION_START) {
    size_t bytes_read = wasm_read_u32_leb128(&binary->data[sec->offset],
                                             &binary->data[binary->size],
                                             &sec->count);
    sec->offset += bytes_read;
    sec->size -= bytes_read;
  }
  return WASM_OK;
}

static WasmBinaryReader s_binary_reader = {
    .begin_section = begin_section,
    .on_reloc = on_reloc,
};

static WasmResult read_binary(uint8_t* data, size_t size, InputBinary* input_info) {
  input_info->data = data;
  input_info->size = size;

  WasmBinaryReader reader;
  WASM_ZERO_MEMORY(reader);
  reader = s_binary_reader;
  reader.user_data = input_info;

  WasmReadBinaryOptions read_options = WASM_READ_BINARY_OPTIONS_DEFAULT;
  return wasm_read_binary(s_allocator, data, size, &reader, 1, &read_options);
}

static void apply_relocations(InputBinary* binary) {
  size_t i;
  for (i = 0; i < binary->relocations.size; i++) {
    Reloc* r = &binary->relocations.data[i];
    uint32_t cur_value = 0;
    switch (r->type) {
      case WASM_RELOC_FUNC_INDEX_LEB:
        wasm_read_u32_leb128(binary->data + r->offset, binary->data + binary->size,
                             &cur_value);
        cur_value += binary->function_index_offset;
        wasm_write_fixed_u32_leb128_raw(binary->data + r->offset,
                                        binary->data + binary->size, cur_value);
        break;
      case WASM_RELOC_FUNC_INDEX_SLEB:
        wasm_read_i32_leb128(binary->data + r->offset, binary->data + binary->size,
                             &cur_value);
        cur_value += binary->function_index_offset;
        wasm_write_fixed_i32_leb128_raw(binary->data + r->offset,
                                        binary->data + binary->size, cur_value);
        break;
      case WASM_RELOC_GLOBAL_INDEX:
        wasm_read_u32_leb128(binary->data + r->offset, binary->data + binary->size,
                             &cur_value);
        cur_value += binary->global_index_offset;
        wasm_write_fixed_u32_leb128_raw(binary->data + r->offset,
                                        binary->data + binary->size, cur_value);
        break;
      default:
        WASM_FATAL("unhandled relocation type: %d\n", r->type);
        break;
    }
  }
}

static void write_combined_function_section(WasmStream* stream, SectionPtrVector* sections) {
  size_t i;
  uint32_t total_count = 0;
  for (i = 0; i < sections->size; i++) {
    SectionPtr sec = sections->data[i];
    sec->binary->function_index_offset = total_count;
    total_count += sec->count;
  }

  wasm_write_u8(stream, WASM_BINARY_SECTION_FUNCTION, "section code");
  uint32_t fixup_offset = stream->offset;
  wasm_write_fixed_u32_leb128(stream, 0, "unknown size");
  uint32_t start = stream->offset;
  wasm_write_u32_leb128(stream, total_count, "element count");

  for (i = 0; i < sections->size; i++) {
    SectionPtr sec = sections->data[i];
    uint32_t count = sec->count;
    uint32_t input_offset = 0;
    uint32_t sig_index = 0;
    const uint8_t* start = &sec->binary->data[sec->offset];
    const uint8_t* end = &sec->binary->data[sec->offset+sec->size];
    while (count--) {
      input_offset += wasm_read_u32_leb128(start+input_offset, end, &sig_index);
      sig_index += sec->binary->type_index_offset;
      wasm_write_u32_leb128(stream, sig_index, "sig");
    }
  }
  wasm_write_fixed_u32_leb128_at(stream, fixup_offset, stream->offset - start, "fixup size");
}

static void write_combined_sections(WasmStream* stream, WasmBinarySection type, SectionPtrVector* sections) {
  if (!sections->size)
    return;

  if (type == WASM_BINARY_SECTION_FUNCTION) {
    write_combined_function_section(stream, sections);
    return;
  }

  size_t i;
  uint32_t total_count = 0;
  uint32_t total_size = 0;

  // Sum section size and element count
  for (i = 0; i < sections->size; i++) {
    SectionPtr sec = sections->data[i];
    if (type == WASM_BINARY_SECTION_TYPE)
      sec->binary->type_index_offset = total_count;
    if (type == WASM_BINARY_SECTION_GLOBAL)
      sec->binary->global_index_offset = total_count;
    if (type == WASM_BINARY_SECTION_CODE)
      apply_relocations(sec->binary);
    total_size += sec->size;
    total_count += sec->count;
  }

  // Total section size includes the element count leb123.
  total_size += wasm_u32_leb128_length(total_count);

  // Write section to stream
  wasm_write_u8(stream, type, "section code");
  wasm_write_u32_leb128(stream, total_size, "section size");
  wasm_write_u32_leb128(stream, total_count, "element count");
  for (i = 0; i < sections->size; i++) {
    SectionPtr sec = sections->data[i];
    uint8_t* start = &sec->binary->data[sec->offset];
    wasm_write_data(stream, start, sec->size, "section content");
  }
}

static void write_binary(WasmStream* stream, InputBinaryVector* inputs) {
  wasm_write_u32(stream, WASM_BINARY_MAGIC, "WASM_BINARY_MAGIC");
  wasm_write_u32(stream, WASM_BINARY_VERSION, "WASM_BINARY_VERSION");

  // Find all the sections of each type
  SectionPtrVector sections[WASM_NUM_BINARY_SECTIONS];
  WASM_ZERO_MEMORY(sections);

  size_t j;
  for (j = 0; j < inputs->size; j++) {
    InputBinary* binary = &inputs->data[j];
    size_t i;
    for (i = 0; i < binary->sections.size; i++) {
      Section* s = &binary->sections.data[i];
      SectionPtrVector* sec_list = &sections[s->type];
      wasm_append_section_ptr(s_allocator, sec_list);
      sec_list->data[sec_list->size-1] = s;
    }
  }

  // Skip USER section for now
  uint32_t t;
  for (t = 1; t < WASM_NUM_BINARY_SECTIONS; t++)
    write_combined_sections(stream, t, &sections[t]);
}

static WasmResult link_intput(InputBinaryVector* inputs) {
  WasmMemoryWriter writer;
  WASM_ZERO_MEMORY(writer);
  if (WASM_FAILED(wasm_init_mem_writer(s_allocator, &writer)))
    WASM_FATAL("unable to open memory writer for writing\n");

  WasmStream* log_stream = NULL;
  if (s_verbose) {
    log_stream = &s_log_stream;
  }

  WasmStream stream;
  wasm_init_stream(&stream, &writer.base, log_stream);
  write_binary(&stream, inputs);

  if (s_verbose)
    wasm_writef(&s_log_stream, "writing file: %s\n", s_outfile);

  wasm_write_output_buffer_to_file(&writer.buf, s_outfile);
  wasm_close_mem_writer(&writer);
  return WASM_OK;
}

int main(int argc, char** argv) {
  s_allocator = &g_wasm_libc_allocator;
  wasm_init_stdio();
  parse_options(argc, argv);

  InputBinaryVector inputs;

  WasmResult result = WASM_OK;
  void* data;
  size_t size;
  uint i;
  for (i = 0; i < s_infiles.size; i++) {
    const char* input_filename = s_infiles.data[i];
    if (s_verbose)
      wasm_writef(&s_log_stream, "reading file: %s\n", input_filename);
    result = wasm_read_file(s_allocator, input_filename, &data, &size);
    if (WASM_FAILED(result))
      exit(1);
    InputBinary* b = wasm_append_binary(s_allocator, &inputs);
    result = read_binary(data, size, b);
    if (WASM_FAILED(result)) {
      WASM_FATAL("error parsing file: %s\n", input_filename);
    }
  }

  result = link_intput(&inputs);
  if (WASM_FAILED(result))
    exit(1);

  wasm_print_allocator_stats(s_allocator);
  wasm_destroy_allocator(s_allocator);
  return result;
}
