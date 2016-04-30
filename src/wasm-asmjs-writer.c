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

#include "wasm-asmjs-writer.h"

#include <assert.h>
#include <inttypes.h>

#include "wasm-allocator.h"
#include "wasm-ast.h"
#include "wasm-config.h"
#include "wasm-stream.h"

/* TODO(binji): share with wasm-ast-writer */

#define INDENT_SIZE 2
#define NO_FORCE_NEWLINE 0
#define FORCE_NEWLINE 1

#define FAIL(msg) assert(!msg)

#define PRIss PRIstringslice
#define SS_ARG WASM_PRINTF_STRING_SLICE_ARG
#define PARAM_SS_ARG(i) SS_ARG(ctx->param_index_to_name.data[i])
#define LOCAL_SS_ARG(i) SS_ARG(ctx->local_index_to_name.data[i])

typedef enum AsmjsType {
  ASMJS_TYPE_ANY = 0,
  ASMJS_TYPE_VOID = 0x1,
  ASMJS_TYPE_FLOATISH = 0x2,
  ASMJS_TYPE_MAYBE_FLOAT = 0x4 | ASMJS_TYPE_FLOATISH,
  ASMJS_TYPE_FLOAT = 0x8 | ASMJS_TYPE_MAYBE_FLOAT,
  ASMJS_TYPE_MAYBE_DOUBLE = 0x10,
  ASMJS_TYPE_EXTERN = 0x20,
  ASMJS_TYPE_DOUBLE = 0x40 | ASMJS_TYPE_MAYBE_DOUBLE | ASMJS_TYPE_EXTERN,
  ASMJS_TYPE_INTISH = 0x80,
  ASMJS_TYPE_INT = 0x100 | ASMJS_TYPE_INTISH,
  ASMJS_TYPE_SIGNED = 0x200 | ASMJS_TYPE_INT | ASMJS_TYPE_EXTERN,
  ASMJS_TYPE_UNSIGNED = 0x400 | ASMJS_TYPE_INT,
  ASMJS_TYPE_FIXNUM = 0x800 | ASMJS_TYPE_SIGNED | ASMJS_TYPE_UNSIGNED,
  /* store types for heap access */
  ASMJS_TYPE_F32_STORE = ASMJS_TYPE_FLOATISH | ASMJS_TYPE_MAYBE_DOUBLE,
  ASMJS_TYPE_F64_STORE = ASMJS_TYPE_MAYBE_FLOAT | ASMJS_TYPE_MAYBE_DOUBLE,
} AsmjsType;

enum {
  FIRST_CHILD = 0,
  ONLY_CHILD = 0,
  SECOND_CHILD = 1,
  THIRD_CHILD = 2,
};

typedef enum Associativity {
  ASSOC_NONE,
  ASSOC_LEFT,
  ASSOC_RIGHT,
} Associativity;

#define PRECEDENCE(V)                                                 \
  V(STATEMENT, LEFT)                                                  \
  V(FUNCTION_ARGS, LEFT)                                              \
  V(COMMA, LEFT)         /* , */                                      \
  V(ASSIGNMENT, RIGHT)   /* = += -= *= /= %= <<= >>= >>>= &= ^= |= */ \
  V(CONDITIONAL, RIGHT)  /* ?: */                                     \
  V(BIT_OR, LEFT)        /* | */                                      \
  V(BIT_XOR, LEFT)       /* ^ */                                      \
  V(BIT_AND, LEFT)       /* & */                                      \
  V(EQ_NE, LEFT)         /* == != */                                  \
  V(LT_GT, LEFT)         /* < <= > >= */                              \
  V(SHIFT, LEFT)         /* << >> >>> */                              \
  V(ADD_SUB, LEFT)       /* + - */                                    \
  V(MUL_DIV, LEFT)       /* * / % */                                  \
  V(UNARY, RIGHT)        /* ! ~ + - */                                \
  V(FUNCTION_CALL, LEFT) /* foo() */                                  \
  V(MEMBER_ACCESS, LEFT) /* foo[] */                                  \
  V(GROUP, NONE)         /* () */

typedef enum Precedence {
#define V(prec, assoc) PREC_##prec,
  PRECEDENCE(V)
#undef V
} Precedence;

typedef enum CoerceType {
  COERCE_NONE,
  COERCE_INTISH_TO_SIGNED,
  COERCE_INTISH_TO_UNSIGNED,
  COERCE_FLOATISH_TO_FLOAT,
  COERCE_DOUBLE_OR_MAYBE_FLOAT_TO_SIGNED,
  COERCE_MAYBE_DOUBLE_TO_DOUBLE,
} CoerceType;

typedef struct CoerceResult {
  CoerceType type;
  Precedence prec;
  int num_parens;
} CoerceResult;

typedef enum NextChar {
  NEXT_CHAR_NONE,
  NEXT_CHAR_SPACE,
  NEXT_CHAR_NEWLINE,
  NEXT_CHAR_FORCE_NEWLINE,
} NextChar;

typedef enum LabelType {
  LABEL_TYPE_BLOCK,
  LABEL_TYPE_LOOP_OUTER,
  LABEL_TYPE_LOOP_INNER,
  LABEL_TYPE_IF,
  LABEL_TYPE_ELSE,
} LabelType;

typedef struct WasmLabelNode {
  const WasmLabel* label;
  const WasmLabel* label_other; /* for loops, this points to the outer label */
  LabelType type;
  struct WasmLabelNode* next;
} WasmLabelNode;

typedef struct Context {
  WasmAllocator* allocator;
  const WasmModule* module;
  const WasmFunc* current_func;
  WasmStream stream;
  WasmResult result;
  int indent;
  NextChar next_char;
  WasmLabelNode* top_label;
  /* mapping from param index to its name, if any, for the current func */
  WasmStringSliceVector param_index_to_name;
  WasmStringSliceVector local_index_to_name;
  uint32_t table_size;
} Context;

typedef struct OpInfo {
  const char* str;
  AsmjsType rtype;
  AsmjsType type1;
  AsmjsType type2;
  Precedence prec;
} OpInfo;

#define OP_INFO(V)                                                       \
  V("+", I32_ADD, INTISH, INT, INT, ADD_SUB)                             \
  V("-", I32_SUB, INTISH, INT, INT, ADD_SUB)                             \
  V("/", I32_DIV_S, INTISH, SIGNED, SIGNED, MUL_DIV)                     \
  V("/", I32_DIV_U, INTISH, UNSIGNED, UNSIGNED, MUL_DIV)                 \
  V("%", I32_REM_S, INTISH, SIGNED, SIGNED, MUL_DIV)                     \
  V("%", I32_REM_U, INTISH, UNSIGNED, UNSIGNED, MUL_DIV)                 \
  V("|", I32_OR, SIGNED, INTISH, INTISH, BIT_OR)                         \
  V("&", I32_AND, SIGNED, INTISH, INTISH, BIT_AND)                       \
  V("^", I32_XOR, SIGNED, INTISH, INTISH, BIT_XOR)                       \
  V("<<", I32_SHL, SIGNED, INTISH, INTISH, SHIFT)                        \
  V(">>", I32_SHR_S, SIGNED, INTISH, INTISH, SHIFT)                      \
  V(">>>", I32_SHR_U, UNSIGNED, INTISH, INTISH, SHIFT)                   \
  V("$$rotr", I32_ROTR, INT, INT, INT, FUNCTION_ARGS)                    \
  V("$$rotl", I32_ROTL, INT, INT, INT, FUNCTION_ARGS)                    \
  V("==", I32_EQ, INT, SIGNED, SIGNED, EQ_NE)                            \
  V("!=", I32_NE, INT, SIGNED, SIGNED, EQ_NE)                            \
  V("<", I32_LT_S, INT, SIGNED, SIGNED, LT_GT)                           \
  V("<=", I32_LE_S, INT, SIGNED, SIGNED, LT_GT)                          \
  V("<", I32_LT_U, INT, UNSIGNED, UNSIGNED, LT_GT)                       \
  V("<=", I32_LE_U, INT, UNSIGNED, UNSIGNED, LT_GT)                      \
  V(">", I32_GT_S, INT, SIGNED, SIGNED, LT_GT)                           \
  V(">=", I32_GE_S, INT, SIGNED, SIGNED, LT_GT)                          \
  V(">", I32_GT_U, INT, UNSIGNED, UNSIGNED, LT_GT)                       \
  V(">=", I32_GE_U, INT, UNSIGNED, UNSIGNED, LT_GT)                      \
  V("$$clz", I32_CLZ, INT, INT, ANY, FUNCTION_ARGS)                      \
  V("$$ctz", I32_CTZ, INT, INT, ANY, FUNCTION_ARGS)                      \
  V("$$popcnt", I32_POPCNT, INT, INT, ANY, FUNCTION_ARGS)                \
  V("+", F32_ADD, FLOATISH, MAYBE_FLOAT, MAYBE_FLOAT, ADD_SUB)           \
  V("-", F32_SUB, FLOATISH, MAYBE_FLOAT, MAYBE_FLOAT, ADD_SUB)           \
  V("*", F32_MUL, FLOATISH, MAYBE_FLOAT, MAYBE_FLOAT, MUL_DIV)           \
  V("/", F32_DIV, FLOATISH, MAYBE_FLOAT, MAYBE_FLOAT, MUL_DIV)           \
  V("$$min", F32_MIN, DOUBLE, DOUBLE, DOUBLE, FUNCTION_ARGS)             \
  V("$$max", F32_MAX, DOUBLE, DOUBLE, DOUBLE, FUNCTION_ARGS)             \
  V("==", F32_EQ, INT, FLOAT, FLOAT, EQ_NE)                              \
  V("!=", F32_NE, INT, FLOAT, FLOAT, EQ_NE)                              \
  V("<", F32_LT, INT, FLOAT, FLOAT, LT_GT)                               \
  V("<=", F32_LE, INT, FLOAT, FLOAT, LT_GT)                              \
  V(">", F32_GT, INT, FLOAT, FLOAT, LT_GT)                               \
  V(">=", F32_GE, INT, FLOAT, FLOAT, LT_GT)                              \
  V("-", F32_NEG, FLOATISH, MAYBE_FLOAT, ANY, UNARY)                     \
  V("$$abs", F32_ABS, FLOAT, MAYBE_FLOAT, ANY, FUNCTION_ARGS)            \
  V("$$sqrt", F32_SQRT, FLOAT, MAYBE_FLOAT, ANY, FUNCTION_ARGS)          \
  V("$$ceil", F32_CEIL, FLOAT, MAYBE_FLOAT, ANY, FUNCTION_ARGS)          \
  V("$$floor", F32_FLOOR, FLOAT, MAYBE_FLOAT, ANY, FUNCTION_ARGS)        \
  V("$$trunc", F32_TRUNC, FLOAT, MAYBE_FLOAT, ANY, FUNCTION_ARGS)        \
  V("$$round", F32_NEAREST, FLOAT, MAYBE_FLOAT, ANY, FUNCTION_ARGS)      \
  V("+", F64_ADD, DOUBLE, DOUBLE, DOUBLE, ADD_SUB)                       \
  V("-", F64_SUB, DOUBLE, MAYBE_DOUBLE, MAYBE_DOUBLE, ADD_SUB)           \
  V("*", F64_MUL, DOUBLE, MAYBE_DOUBLE, MAYBE_DOUBLE, MUL_DIV)           \
  V("/", F64_DIV, DOUBLE, MAYBE_DOUBLE, MAYBE_DOUBLE, MUL_DIV)           \
  V("$$min", F64_MIN, DOUBLE, DOUBLE, DOUBLE, FUNCTION_ARGS)             \
  V("$$max", F64_MAX, DOUBLE, DOUBLE, DOUBLE, FUNCTION_ARGS)             \
  V("==", F64_EQ, INT, DOUBLE, DOUBLE, EQ_NE)                            \
  V("!=", F64_NE, INT, DOUBLE, DOUBLE, EQ_NE)                            \
  V("<", F64_LT, INT, DOUBLE, DOUBLE, LT_GT)                             \
  V("<=", F64_LE, INT, DOUBLE, DOUBLE, LT_GT)                            \
  V(">", F64_GT, INT, DOUBLE, DOUBLE, LT_GT)                             \
  V(">=", F64_GE, INT, DOUBLE, DOUBLE, LT_GT)                            \
  V("-", F64_NEG, DOUBLE, MAYBE_DOUBLE, ANY, UNARY)                      \
  V("$$abs", F64_ABS, DOUBLE, MAYBE_DOUBLE, ANY, FUNCTION_ARGS)          \
  V("$$sqrt", F64_SQRT, DOUBLE, MAYBE_DOUBLE, ANY, FUNCTION_ARGS)        \
  V("$$ceil", F64_CEIL, DOUBLE, MAYBE_DOUBLE, ANY, FUNCTION_ARGS)        \
  V("$$floor", F64_FLOOR, DOUBLE, MAYBE_DOUBLE, ANY, FUNCTION_ARGS)      \
  V("$$trunc", F64_TRUNC, DOUBLE, MAYBE_DOUBLE, ANY, FUNCTION_ARGS)      \
  V("$$round", F64_NEAREST, DOUBLE, MAYBE_DOUBLE, ANY, FUNCTION_ARGS)    \
  V("~~", I32_TRUNC_S_F32, SIGNED, MAYBE_FLOAT, ANY, UNARY)              \
  V("~~", I32_TRUNC_S_F64, SIGNED, DOUBLE, ANY, UNARY)                   \
  V("~~", I32_TRUNC_U_F32, SIGNED, MAYBE_FLOAT, ANY, UNARY)              \
  V("~~", I32_TRUNC_U_F64, SIGNED, DOUBLE, ANY, UNARY)                   \
  V("$$fround", F32_CONVERT_S_I32, FLOAT, INT, ANY, FUNCTION_ARGS)       \
  V("$$fround", F32_CONVERT_U_I32, FLOAT, INT, ANY, FUNCTION_ARGS)       \
  V("+", F64_CONVERT_S_I32, DOUBLE, INT, ANY, UNARY)                     \
  V("+", F64_CONVERT_U_I32, DOUBLE, INT, ANY, UNARY)                     \
  V("+", F64_PROMOTE_F32, DOUBLE, FLOATISH, ANY, UNARY)                  \
  V("$$fround", F32_DEMOTE_F64, FLOAT, MAYBE_DOUBLE, ANY, FUNCTION_ARGS) \
  V("$$itof32", F32_REINTERPRET_I32, FLOAT, INT, ANY, FUNCTION_ARGS)     \
  V("$$ftoi32", I32_REINTERPRET_F32, INT, FLOAT, ANY, FUNCTION_ARGS)     \
  V("$MEM8", I32_LOAD8_S, INTISH, INTISH, ANY, STATEMENT)                \
  V("$MEMU8", I32_LOAD8_U, INTISH, INTISH, ANY, STATEMENT)               \
  V("$MEM16", I32_LOAD16_S, INTISH, INTISH, ANY, STATEMENT)              \
  V("$MEMU16", I32_LOAD16_U, INTISH, INTISH, ANY, STATEMENT)             \
  V("$MEM32", I32_LOAD, INTISH, INTISH, ANY, STATEMENT)                  \
  V("$MEMF32", F32_LOAD, MAYBE_FLOAT, INTISH, ANY, STATEMENT)            \
  V("$MEMF64", F64_LOAD, MAYBE_DOUBLE, INTISH, ANY, STATEMENT)           \
  V("$MEM8", I32_STORE8, INTISH, INTISH, ANY, ASSIGNMENT)                \
  V("$MEM16", I32_STORE16, INTISH, INTISH, ANY, ASSIGNMENT)              \
  V("$MEM32", I32_STORE, INTISH, INTISH, ANY, ASSIGNMENT)                \
  V("$MEMF32", F32_STORE, F32_STORE, INTISH, F32_STORE, ASSIGNMENT)      \
  V("$MEMF64", F64_STORE, F64_STORE, INTISH, F64_STORE, ASSIGNMENT)

static OpInfo s_opcode_info[] = {
#define V(str, code, tr, t1, t2, prec)                           \
  [WASM_OPCODE_##code] = {str, ASMJS_TYPE_##tr, ASMJS_TYPE_##t1, \
                          ASMJS_TYPE_##t2, PREC_##prec},
    OP_INFO(V)
#undef V
};

#define SHIFT_AMOUNT(V) \
  V(I32_LOAD8_S, 0)     \
  V(I32_LOAD8_U, 0)     \
  V(I32_LOAD16_S, 1)    \
  V(I32_LOAD16_U, 1)    \
  V(I32_LOAD, 2)        \
  V(F32_LOAD, 2)        \
  V(F64_LOAD, 3)        \
  V(I32_STORE8, 0)      \
  V(I32_STORE16, 1)     \
  V(I32_STORE, 2)       \
  V(F32_STORE, 2)       \
  V(F64_STORE, 3)

static uint32_t s_opcode_shift_amount[] = {
#define V(code, shift) [WASM_OPCODE_##code] = shift,
    SHIFT_AMOUNT(V)
#undef V
};

static Associativity s_prec_assoc[] = {
#define V(prec, assoc) [PREC_##prec] = ASSOC_##assoc,
    PRECEDENCE(V)
#undef V
};

#define DEFINE_BITCAST(name, src, dst) \
  static WASM_INLINE dst name(src x) { \
    dst result;                        \
    memcpy(&result, &x, sizeof(dst));  \
    return result;                     \
  }

DEFINE_BITCAST(bitcast_u32_to_f32, uint32_t, float)
DEFINE_BITCAST(bitcast_u64_to_f64, uint64_t, double)

static uint32_t next_power_of_two(uint32_t x) {
  return 1 << (sizeof(uint32_t) * 8 - wasm_clz_u32(x - 1));
}

static WasmLabelNode* find_label_by_name(WasmLabelNode* top_label,
                                         const WasmStringSlice* name) {
  WasmLabelNode* node = top_label;
  while (node) {
    if (node->label && wasm_string_slices_are_equal(node->label, name))
      return node;
    node = node->next;
  }
  return NULL;
}

static WasmLabelNode* find_label_by_var(WasmLabelNode* top_label,
                                        const WasmVar* var) {
  assert(var->type == WASM_VAR_TYPE_NAME);
  return find_label_by_name(top_label, &var->name);
}

static void push_label(Context* ctx,
                       WasmLabelNode* node,
                       const WasmLabel* label,
                       LabelType label_type) {
  assert(label);
  node->label = label;
  node->label_other = label;
  node->next = ctx->top_label;
  node->type = label_type;
  ctx->top_label = node;
}

static void push_label_with_other(Context* ctx,
                                  WasmLabelNode* node,
                                  const WasmLabel* label,
                                  const WasmLabel* label_other,
                                  LabelType label_type) {
  assert(label);
  node->label = label;
  node->label_other = label_other;
  node->next = ctx->top_label;
  node->type = label_type;
  ctx->top_label = node;
}

static void pop_label(Context* ctx) {
  assert(ctx->top_label);
  ctx->top_label = ctx->top_label->next;
}

static void indent(Context* ctx) {
  ctx->indent += INDENT_SIZE;
}

static void dedent(Context* ctx) {
  ctx->indent -= INDENT_SIZE;
  assert(ctx->indent >= 0);
}

static void write_indent(Context* ctx) {
  static char s_indent[] =
      "                                                                       "
      "                                                                       ";
  static size_t s_indent_len = sizeof(s_indent) - 1;
  size_t indent = ctx->indent;
  while (indent > s_indent_len) {
    wasm_write_data(&ctx->stream, s_indent, s_indent_len, NULL);
    indent -= s_indent_len;
  }
  if (indent > 0) {
    wasm_write_data(&ctx->stream, s_indent, indent, NULL);
  }
}

static void write_next_char(Context* ctx) {
  switch (ctx->next_char) {
    case NEXT_CHAR_SPACE:
      wasm_write_data(&ctx->stream, " ", 1, NULL);
      break;
    case NEXT_CHAR_NEWLINE:
    case NEXT_CHAR_FORCE_NEWLINE:
      wasm_write_data(&ctx->stream, "\n", 1, NULL);
      write_indent(ctx);
      break;

    default:
    case NEXT_CHAR_NONE:
      break;
  }
  ctx->next_char = NEXT_CHAR_NONE;
}

static void write_data_with_next_char(Context* ctx,
                                      const void* src,
                                      size_t size) {
  write_next_char(ctx);
  wasm_write_data(&ctx->stream, src, size, NULL);
}

static void WASM_PRINTF_FORMAT(2, 3)
    writef_nl(Context* ctx, const char* format, ...) {
  WASM_SNPRINTF_ALLOCA(buffer, length, format);
  /* default to following newline */
  write_data_with_next_char(ctx, buffer, length);
  ctx->next_char = NEXT_CHAR_NEWLINE;
}

static void WASM_PRINTF_FORMAT(2, 3)
    writef(Context* ctx, const char* format, ...) {
  WASM_SNPRINTF_ALLOCA(buffer, length, format);
  /* default to following newline */
  write_data_with_next_char(ctx, buffer, length);
  ctx->next_char = NEXT_CHAR_NONE;
}

static void write_string_slice(Context* ctx,
                               const WasmStringSlice* str,
                               NextChar next_char) {
  writef_nl(ctx, PRIstringslice, WASM_PRINTF_STRING_SLICE_ARG(*str));
  ctx->next_char = next_char;
}

static void write_putc(Context* ctx, char c) {
  wasm_write_data(&ctx->stream, &c, 1, NULL);
}

static void write_puts(Context* ctx, const char* s) {
  size_t len = strlen(s);
  write_data_with_next_char(ctx, s, len);
  ctx->next_char = NEXT_CHAR_NONE;
}

static void write_open_paren(Context* ctx) {
  char c = '(';
  write_data_with_next_char(ctx, &c, 1);
  ctx->next_char = NEXT_CHAR_NONE;
}

static void write_close_paren(Context* ctx) {
  char c = ')';
  write_data_with_next_char(ctx, &c, 1);
  ctx->next_char = NEXT_CHAR_NONE;
}

static void write_newline(Context* ctx, WasmBool force) {
  if (ctx->next_char == NEXT_CHAR_FORCE_NEWLINE)
    write_next_char(ctx);
  ctx->next_char = force ? NEXT_CHAR_FORCE_NEWLINE : NEXT_CHAR_NEWLINE;
}

static WasmBool is_asmjs_type(AsmjsType t, AsmjsType expected) {
  return (t & expected) == expected;
}

static WasmBool is_multiplicative_const(const WasmExpr* expr) {
  return expr->type == WASM_EXPR_TYPE_CONST &&
         expr->const_.type == WASM_TYPE_I32 &&
         (int32_t)expr->const_.u32 > -(1 << 20) &&
         (int32_t)expr->const_.u32 < (1 << 20);
}

static WasmBool has_precedence_over(Precedence parent,
                                    Precedence child,
                                    int child_index) {
  if (parent == child) {
    Associativity assoc = s_prec_assoc[parent];
    assert(child_index < 2);
    assert(assoc != ASSOC_NONE);
    if (assoc == ASSOC_LEFT) {
      return child_index == SECOND_CHILD;
    } else if (assoc == ASSOC_RIGHT) {
      return child_index == FIRST_CHILD;
    }
  }
  return parent > child;
}

static CoerceResult begin_coerce(Context* ctx,
                                 AsmjsType expected,
                                 AsmjsType type,
                                 Precedence parent_prec,
                                 Precedence prec,
                                 int child_index) {
  CoerceResult result;
  result.type = COERCE_NONE;
  result.num_parens = 0;
  result.prec = PREC_STATEMENT;
  const char* coerce_prefix = NULL;
  WasmBool outer_parens = WASM_FALSE;
  WasmBool inner_parens = WASM_FALSE;
  if (is_asmjs_type(expected, ASMJS_TYPE_INTISH) &&
      !is_asmjs_type(type, expected)) {
    assert(is_asmjs_type(type, ASMJS_TYPE_INTISH));
    if (expected == ASMJS_TYPE_UNSIGNED) {
      result.type = COERCE_INTISH_TO_UNSIGNED;
      result.prec = PREC_SHIFT;
    } else {
      result.type = COERCE_INTISH_TO_SIGNED;
      result.prec = PREC_BIT_OR;
    }
    outer_parens = has_precedence_over(parent_prec, result.prec, child_index);
    inner_parens = has_precedence_over(result.prec, prec, FIRST_CHILD);
  } else if (is_asmjs_type(expected, ASMJS_TYPE_MAYBE_DOUBLE) &&
             !is_asmjs_type(type, expected)) {
    assert(is_asmjs_type(type, ASMJS_TYPE_MAYBE_DOUBLE));
    result.type = COERCE_MAYBE_DOUBLE_TO_DOUBLE;
    result.prec = PREC_UNARY;
    coerce_prefix = "+";
    outer_parens = has_precedence_over(parent_prec, result.prec, child_index);
    inner_parens = has_precedence_over(result.prec, prec, FIRST_CHILD);
  } else if (is_asmjs_type(expected, ASMJS_TYPE_FLOATISH) &&
             !is_asmjs_type(type, expected)) {
    assert(is_asmjs_type(type, ASMJS_TYPE_FLOATISH));
    result.type = COERCE_FLOATISH_TO_FLOAT;
    result.prec = PREC_FUNCTION_ARGS;
    coerce_prefix = "$$fround(";
  } else {
    outer_parens = has_precedence_over(parent_prec, prec, child_index);
  }

  if (outer_parens) {
    write_open_paren(ctx);
    result.num_parens++;
  }

  if (coerce_prefix)
    write_puts(ctx, coerce_prefix);

  if (inner_parens) {
    write_open_paren(ctx);
    result.num_parens++;
  }

  return result;
}

static void end_coerce(Context* ctx, CoerceResult coerce) {
  if (coerce.num_parens > 1)
    write_close_paren(ctx);
  switch (coerce.type) {
    case COERCE_INTISH_TO_SIGNED:
      write_puts(ctx, "|0");
      break;
    case COERCE_INTISH_TO_UNSIGNED:
      write_puts(ctx, ">>>0");
      break;
    case COERCE_FLOATISH_TO_FLOAT:
      write_puts(ctx, ")");
      break;
    default: break;
  }
  if (coerce.num_parens > 0)
    write_close_paren(ctx);
}

static AsmjsType wasm_type_to_asmjs_type(WasmType type, AsmjsType i32_type) {
  switch (type) {
    case WASM_TYPE_VOID: return ASMJS_TYPE_VOID;
    case WASM_TYPE_I32: return i32_type;
    case WASM_TYPE_F32: return ASMJS_TYPE_FLOAT;
    case WASM_TYPE_F64: return ASMJS_TYPE_DOUBLE;
    default:
      FAIL("bad wasm type");
      return ASMJS_TYPE_ANY;
  }
}

static void write_argument_list(Context*,
                                const WasmFuncSignature*,
                                const WasmExpr*);
static void write_statement_list(Context*, const WasmExpr*);
static void write_expr(Context*,
                       const WasmExpr*,
                       AsmjsType expected_type,
                       Precedence prec,
                       int child_index);

static void write_const(Context* ctx,
                        const WasmConst* const_,
                        AsmjsType expected_type) {
  switch (const_->type) {
    case WASM_TYPE_I32:
      if (expected_type == ASMJS_TYPE_UNSIGNED) {
        writef(ctx, "%u", const_->u32);
      } else {
        writef(ctx, "%d", (int32_t)const_->u32);
      }
      break;
    case WASM_TYPE_F32:
      writef(ctx, "$$fround(%f)", bitcast_u32_to_f32(const_->f32_bits));
      break;
    case WASM_TYPE_F64:
      /* TODO(binji): nicer double output. Asm.js requires a `.` in the value
       * so it can be recognized as a double. # does that, but it also prints
       * too much precision (e.g. 4.00000). */
      writef(ctx, "%#f", bitcast_u64_to_f64(const_->f64_bits));
      break;
    default:
      FAIL("bad const type");
      break;
  }
}

static void write_expr(Context* ctx,
                       const WasmExpr* expr,
                       AsmjsType expected_type,
                       Precedence parent_prec,
                       int child_index) {
  CoerceResult coerce;
  switch (expr->type) {
    case WASM_EXPR_TYPE_BINARY: {
      WasmOpcode opcode = expr->binary.opcode;
      OpInfo info = s_opcode_info[opcode];
      Precedence prec = info.prec;
      WasmExpr* left = expr->binary.left;
      WasmExpr* right = expr->binary.right;
      switch (opcode) {
        case WASM_OPCODE_I32_ADD:
        case WASM_OPCODE_I32_SUB:
          /* TODO(binji): for i32_{add,sub}, allow left and right to be INTISH,
           * as long as there are less than 2**20 consecutive additive
           * operations */
        case WASM_OPCODE_I32_DIV_S:
        case WASM_OPCODE_I32_REM_S:
        case WASM_OPCODE_I32_DIV_U:
        case WASM_OPCODE_I32_REM_U:
        case WASM_OPCODE_I32_AND:
        case WASM_OPCODE_I32_OR:
        case WASM_OPCODE_I32_XOR:
        case WASM_OPCODE_I32_SHL:
        case WASM_OPCODE_I32_SHR_S:
        case WASM_OPCODE_I32_SHR_U:
        case WASM_OPCODE_F32_ADD:
        case WASM_OPCODE_F32_SUB:
        case WASM_OPCODE_F32_MUL:
        case WASM_OPCODE_F32_DIV:
        case WASM_OPCODE_F64_ADD:
        case WASM_OPCODE_F64_SUB:
        case WASM_OPCODE_F64_MUL:
        case WASM_OPCODE_F64_DIV:
          coerce = begin_coerce(ctx, expected_type, info.rtype, parent_prec,
                                prec, child_index);
          write_expr(ctx, left, info.type1, prec, FIRST_CHILD);
          writef(ctx, " %s ", info.str);
          write_expr(ctx, right, info.type2, prec, SECOND_CHILD);
          end_coerce(ctx, coerce);
          break;

        case WASM_OPCODE_I32_MUL: {
          if (is_multiplicative_const(left) || is_multiplicative_const(right)) {
            coerce = begin_coerce(ctx, expected_type, ASMJS_TYPE_INTISH,
                                  parent_prec, PREC_MUL_DIV, child_index);
            write_expr(ctx, left, ASMJS_TYPE_INT, PREC_MUL_DIV, FIRST_CHILD);
            write_puts(ctx, " * ");
            write_expr(ctx, right, ASMJS_TYPE_INT, PREC_MUL_DIV, SECOND_CHILD);
            end_coerce(ctx, coerce);
          } else {
            coerce = begin_coerce(ctx, expected_type, ASMJS_TYPE_SIGNED,
                                  parent_prec, PREC_FUNCTION_ARGS, child_index);
            write_puts(ctx, "$$imul(");
            write_expr(ctx, left, ASMJS_TYPE_INT, PREC_FUNCTION_ARGS,
                       FIRST_CHILD);
            write_puts(ctx, ", ");
            write_expr(ctx, right, ASMJS_TYPE_INT, PREC_FUNCTION_ARGS,
                       SECOND_CHILD);
            write_puts(ctx, ")");
            end_coerce(ctx, coerce);
          }
          break;
        }

        case WASM_OPCODE_I32_ROTR:
        case WASM_OPCODE_I32_ROTL:
        case WASM_OPCODE_F32_MIN:
        case WASM_OPCODE_F64_MIN:
        case WASM_OPCODE_F32_MAX:
        case WASM_OPCODE_F64_MAX:
          coerce = begin_coerce(ctx, expected_type, info.rtype, parent_prec,
                                prec, child_index);
          write_puts(ctx, info.str);
          write_putc(ctx, '(');
          write_expr(ctx, left, info.type1, prec, FIRST_CHILD);
          write_puts(ctx, ", ");
          write_expr(ctx, right, info.type2, prec, SECOND_CHILD);
          write_putc(ctx, ')');
          end_coerce(ctx, coerce);
          break;

        default:
          FAIL("bad binary opcode");
      }
      break;
    }

    case WASM_EXPR_TYPE_BLOCK: {
      WasmLabelNode node;
      push_label(ctx, &node, &expr->block.label, LABEL_TYPE_BLOCK);
      writef_nl(ctx, PRIss ": {", SS_ARG(expr->block.label));
      indent(ctx);
      write_statement_list(ctx, expr->block.first);
      dedent(ctx);
      write_puts(ctx, "}");
      pop_label(ctx);
      break;
    }

    case WASM_EXPR_TYPE_BR: {
      WasmLabelNode* node = find_label_by_var(ctx->top_label, &expr->br.var);
      assert(node);
      write_puts(ctx,
                 node->type == LABEL_TYPE_LOOP_INNER ? "continue " : "break ");
      write_string_slice(ctx, node->label_other, NEXT_CHAR_NONE);
      break;
    }

    case WASM_EXPR_TYPE_BR_IF: {
      WasmLabelNode* node = find_label_by_var(ctx->top_label, &expr->br_if.var);
      assert(node);
      write_puts(ctx, "if (");
      write_expr(ctx, expr->br_if.cond, ASMJS_TYPE_INT, PREC_STATEMENT,
                 ONLY_CHILD);
      writef(ctx, ") %s",
             node->type == LABEL_TYPE_LOOP_INNER ? "continue " : "break ");
      write_string_slice(ctx, node->label_other, NEXT_CHAR_NONE);
      break;
    }

    case WASM_EXPR_TYPE_BR_TABLE:
      /* TODO */
      break;

    case WASM_EXPR_TYPE_CALL: {
      const WasmFunc* callee =
          wasm_get_func_by_var(ctx->module, &expr->call.var);
      const WasmFuncSignature* sig =
          wasm_decl_get_signature(ctx->module, &callee->decl);
      AsmjsType rtype =
          wasm_type_to_asmjs_type(sig->result_type, ASMJS_TYPE_INT);
      coerce = begin_coerce(ctx, expected_type, rtype, parent_prec,
                            PREC_FUNCTION_CALL, child_index);
      write_string_slice(ctx, &expr->call.var.name, NEXT_CHAR_NONE);
      write_puts(ctx, "(");
      write_argument_list(ctx, sig, expr->call.first_arg);
      write_puts(ctx, ")");
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_CALL_IMPORT: {
      const WasmImport* callee =
          wasm_get_import_by_var(ctx->module, &expr->call.var);
      const WasmFuncSignature* sig =
          wasm_decl_get_signature(ctx->module, &callee->decl);
      AsmjsType rtype =
          wasm_type_to_asmjs_type(sig->result_type, ASMJS_TYPE_INT);
      coerce = begin_coerce(ctx, expected_type, rtype, parent_prec,
                            PREC_FUNCTION_CALL, child_index);
      write_string_slice(ctx, &expr->call.var.name, NEXT_CHAR_NONE);
      write_puts(ctx, "(");
      write_argument_list(ctx, sig, expr->call.first_arg);
      write_puts(ctx, ")");
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_CALL_INDIRECT: {
      const WasmFuncType* func_type =
          wasm_get_func_type_by_var(ctx->module, &expr->call_indirect.var);
      const WasmFuncSignature* sig = &func_type->sig;
      AsmjsType rtype =
          wasm_type_to_asmjs_type(sig->result_type, ASMJS_TYPE_INT);
      coerce = begin_coerce(ctx, expected_type, rtype, parent_prec,
                            PREC_FUNCTION_CALL, child_index);
      write_puts(ctx, "$$TABLE[");
      write_expr(ctx, expr->call_indirect.expr, ASMJS_TYPE_INTISH, PREC_BIT_AND,
                 ONLY_CHILD);
      writef(ctx, " & %u](", ctx->table_size - 1);
      write_argument_list(ctx, sig, expr->call_indirect.first_arg);
      write_puts(ctx, ")");
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_COMPARE: {
      OpInfo info = s_opcode_info[expr->compare.opcode];
      coerce = begin_coerce(ctx, expected_type, info.rtype, parent_prec,
                            info.prec, child_index);
      write_expr(ctx, expr->compare.left, info.type1, info.prec, FIRST_CHILD);
      writef(ctx, " %s ", info.str);
      write_expr(ctx, expr->compare.right, info.type2, info.prec, SECOND_CHILD);
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_CONST:
      write_const(ctx, &expr->const_, expected_type);
      break;

    case WASM_EXPR_TYPE_CONVERT: {
      OpInfo info = s_opcode_info[expr->convert.opcode];
      coerce = begin_coerce(ctx, expected_type, info.rtype, parent_prec,
                            info.prec, child_index);
      if (info.prec == PREC_FUNCTION_ARGS) {
        write_puts(ctx, info.str);
        write_putc(ctx, '(');
        write_expr(ctx, expr->convert.expr, info.type1, PREC_STATEMENT,
                   ONLY_CHILD);
        write_putc(ctx, ')');
      } else if (info.prec == PREC_UNARY) {
        write_puts(ctx, info.str);
        write_expr(ctx, expr->convert.expr, info.type1, info.prec, ONLY_CHILD);
      }
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_GET_LOCAL: {
      WasmType local_type;
      WasmResult result = wasm_get_local_type_by_var(
          ctx->module, ctx->current_func, &expr->get_local.var, &local_type);
      WASM_USE(result);
      assert(WASM_SUCCEEDED(result));
      coerce = begin_coerce(ctx, expected_type,
                            wasm_type_to_asmjs_type(local_type, ASMJS_TYPE_INT),
                            parent_prec, PREC_GROUP, child_index);
      write_string_slice(ctx, &expr->get_local.var.name, NEXT_CHAR_NONE);
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_GROW_MEMORY:
      /* TODO */
      break;

    case WASM_EXPR_TYPE_IF: {
      WasmLabelNode node;
      push_label(ctx, &node, &expr->if_.true_.label, LABEL_TYPE_IF);
      writef(ctx, PRIss ": if (", SS_ARG(expr->if_.true_.label));
      write_expr(ctx, expr->if_.cond, ASMJS_TYPE_INT, PREC_STATEMENT,
                 ONLY_CHILD);
      write_puts(ctx, ") {");
      write_newline(ctx, WASM_TRUE);
      indent(ctx);
      write_statement_list(ctx, expr->if_.true_.first);
      dedent(ctx);
      write_puts(ctx, "}");
      pop_label(ctx);
      break;
    }

    case WASM_EXPR_TYPE_IF_ELSE: {
      WasmLabelNode node;
      push_label(ctx, &node, &expr->if_else.true_.label, LABEL_TYPE_IF);
      writef(ctx, PRIss ": if (", SS_ARG(expr->if_else.true_.label));
      write_expr(ctx, expr->if_else.cond, ASMJS_TYPE_INT, PREC_STATEMENT,
                 ONLY_CHILD);
      write_puts(ctx, ") {");
      write_newline(ctx, WASM_TRUE);
      indent(ctx);
      write_statement_list(ctx, expr->if_else.true_.first);
      dedent(ctx);
      pop_label(ctx);
      /* the false block label uses the true block's label; they break to the
       * same place */
      push_label_with_other(ctx, &node, &expr->if_else.false_.label,
                            &expr->if_else.true_.label, LABEL_TYPE_ELSE);
      write_puts(ctx, "} else {");
      write_newline(ctx, WASM_TRUE);
      indent(ctx);
      write_statement_list(ctx, expr->if_else.false_.first);
      dedent(ctx);
      write_puts(ctx, "}");
      pop_label(ctx);
      break;
    }

    case WASM_EXPR_TYPE_LOAD: {
      WasmOpcode opcode = expr->load.opcode;
      OpInfo info = s_opcode_info[opcode];
      uint32_t shift_amount = s_opcode_shift_amount[opcode];
      coerce = begin_coerce(ctx, expected_type, expected_type, parent_prec,
                            PREC_MEMBER_ACCESS, child_index);
      writef(ctx, "%s[", info.str);
      if (shift_amount != 0) {
        write_expr(ctx, expr->load.addr, info.type1, PREC_SHIFT, ONLY_CHILD);
        writef(ctx, ">>%u", shift_amount);
      } else {
        write_expr(ctx, expr->load.addr, info.type1, info.prec, ONLY_CHILD);
      }
      write_puts(ctx, "]");
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_LOOP: {
      WasmLabelNode outer;
      WasmLabelNode inner;
      /* the inner label uses the outer label's name; if you break to it, it
       * will turn into a continue */
      push_label(ctx, &outer, &expr->loop.outer, LABEL_TYPE_LOOP_OUTER);
      push_label_with_other(ctx, &inner, &expr->loop.inner, &expr->loop.outer,
                            LABEL_TYPE_LOOP_INNER);
      writef_nl(ctx, PRIss ": while (1) {", SS_ARG(expr->loop.outer));
      indent(ctx);
      write_statement_list(ctx, expr->loop.first);
      dedent(ctx);
      write_puts(ctx, "}");
      pop_label(ctx);
      pop_label(ctx);
      break;
    }

    case WASM_EXPR_TYPE_CURRENT_MEMORY:
      /* TODO */
      break;

    case WASM_EXPR_TYPE_NOP:
      write_puts(ctx, "/*nop*/");
      break;

    case WASM_EXPR_TYPE_RETURN: {
      WasmType result_type =
          wasm_get_result_type(ctx->module, ctx->current_func);
      write_puts(ctx, "return ");
      write_expr(ctx, expr->return_.expr,
                 wasm_type_to_asmjs_type(result_type, ASMJS_TYPE_SIGNED),
                 PREC_STATEMENT, ONLY_CHILD);
      break;
    }

    case WASM_EXPR_TYPE_SELECT:
      /* select has already been lowered to a statement by the
       * lower_expressions pass. This means we can use ?: because the
       * difference in short-circuiting behavior and evaluation order won't be
       * observed */
      coerce = begin_coerce(ctx, expected_type, expected_type, parent_prec,
                            PREC_CONDITIONAL, child_index);
      write_expr(ctx, expr->select.cond, ASMJS_TYPE_INT, PREC_CONDITIONAL,
                 FIRST_CHILD);
      write_puts(ctx, " ? ");
      write_expr(ctx, expr->select.true_, expected_type, PREC_CONDITIONAL,
                 SECOND_CHILD);
      write_puts(ctx, " : ");
      write_expr(ctx, expr->select.false_, expected_type, PREC_CONDITIONAL,
                 THIRD_CHILD);
      end_coerce(ctx, coerce);
      break;

    case WASM_EXPR_TYPE_SET_LOCAL: {
      WasmType local_type;
      WasmResult result = wasm_get_local_type_by_var(
          ctx->module, ctx->current_func, &expr->set_local.var, &local_type);
      WASM_USE(result);
      assert(WASM_SUCCEEDED(result));
      AsmjsType rtype = wasm_type_to_asmjs_type(local_type, ASMJS_TYPE_INT);
      coerce = begin_coerce(ctx, expected_type, rtype, parent_prec,
                            PREC_ASSIGNMENT, child_index);
      writef(ctx, PRIss " = ", SS_ARG(expr->set_local.var.name));
      write_expr(ctx, expr->set_local.expr, rtype, PREC_ASSIGNMENT,
                 SECOND_CHILD);
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_STORE: {
      WasmOpcode opcode = expr->store.opcode;
      OpInfo info = s_opcode_info[opcode];
      uint32_t shift_amount = s_opcode_shift_amount[opcode];
      coerce = begin_coerce(ctx, expected_type, info.rtype, parent_prec,
                            PREC_ASSIGNMENT, child_index);
      writef(ctx, "%s[", info.str);
      if (shift_amount != 0) {
        write_expr(ctx, expr->store.addr, info.type1, PREC_SHIFT, FIRST_CHILD);
        writef(ctx, ">>%u", shift_amount);
      } else {
        write_expr(ctx, expr->store.addr, info.type1, PREC_STATEMENT,
                   FIRST_CHILD);
      }
      write_puts(ctx, "] = ");
      write_expr(ctx, expr->store.value, info.type2, PREC_ASSIGNMENT,
                 SECOND_CHILD);
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_UNARY: {
      OpInfo info = s_opcode_info[expr->unary.opcode];
      coerce = begin_coerce(ctx, expected_type, info.rtype, parent_prec,
                            info.prec, child_index);
      if (info.prec == PREC_FUNCTION_ARGS) {
        write_puts(ctx, info.str);
        write_putc(ctx, '(');
        write_expr(ctx, expr->unary.expr, info.type1, info.prec, FIRST_CHILD);
        write_putc(ctx, ')');
      } else {
        write_puts(ctx, info.str);
        write_expr(ctx, expr->unary.expr, info.type1, info.prec, FIRST_CHILD);
      }
      end_coerce(ctx, coerce);
      break;
    }

    case WASM_EXPR_TYPE_UNREACHABLE:
      write_puts(ctx, "/*unreachable*/");
      break;

    default:
      FAIL("bad expr");
      break;
  }
}

static void write_argument_list(Context* ctx,
                                const WasmFuncSignature* sig,
                                const WasmExpr* first) {
  const WasmExpr* expr;
  size_t i;
  for (i = 0, expr = first; expr; ++i, expr = expr->next) {
    WasmType arg_type = sig->param_types.data[i];
    write_expr(ctx, expr, wasm_type_to_asmjs_type(arg_type, ASMJS_TYPE_INT),
               PREC_STATEMENT, i);
    if (expr->next)
      write_puts(ctx, ", ");
  }
}

static void write_statement_list(Context* ctx, const WasmExpr* first) {
  static WasmBool s_no_semicolon[WASM_NUM_EXPR_TYPES] = {
    [WASM_EXPR_TYPE_BLOCK] = WASM_TRUE,
    [WASM_EXPR_TYPE_LOOP] = WASM_TRUE,
    [WASM_EXPR_TYPE_IF] = WASM_TRUE,
    [WASM_EXPR_TYPE_IF_ELSE] = WASM_TRUE,
  };
  const WasmExpr* expr;
  for (expr = first; expr; expr = expr->next) {
    write_expr(ctx, expr, ASMJS_TYPE_ANY, PREC_STATEMENT, ONLY_CHILD);
    if (!s_no_semicolon[expr->type])
      write_puts(ctx, ";");
    write_newline(ctx, WASM_TRUE);
  }
}

static void write_param_list(Context* ctx, const WasmFunc* func) {
  size_t num_params = wasm_get_num_params(ctx->module, func);
  size_t i;
  for (i = 0; i < num_params; ++i) {
    write_string_slice(ctx, &ctx->param_index_to_name.data[i], NEXT_CHAR_NONE);
    if (i != num_params - 1)
      write_puts(ctx, ", ");
  }
}

static void write_param_type_annotations(Context* ctx, const WasmFunc* func) {
  size_t num_params = wasm_get_num_params(ctx->module, func);
  size_t i;
  for (i = 0; i < num_params; ++i) {
    WasmType type = wasm_get_param_type(ctx->module, func, i);
    WasmStringSlice* name = &ctx->param_index_to_name.data[i];
    write_string_slice(ctx, name, NEXT_CHAR_SPACE);
    switch (type) {
      case WASM_TYPE_I32:
        writef_nl(ctx, "= " PRIss "|0;", SS_ARG(*name));
        break;
      case WASM_TYPE_F32:
        writef_nl(ctx, "= $$fround(" PRIss ");", SS_ARG(*name));
        break;
      case WASM_TYPE_F64:
        writef_nl(ctx, "= +" PRIss ";", SS_ARG(*name));
        break;
      default:
        FAIL("invalid param type");
    }
    write_newline(ctx, WASM_TRUE);
  }
}

static void write_locals(Context* ctx, const WasmFunc* func) {
  size_t num_locals = func->local_types.size;
  if (num_locals > 0) {
    write_puts(ctx, "var ");
    size_t i;
    for (i = 0; i < num_locals; ++i) {
      WasmType type = wasm_get_local_type(func, i);
      write_string_slice(ctx, &ctx->local_index_to_name.data[i],
                         NEXT_CHAR_SPACE);
      switch (type) {
        case WASM_TYPE_I32:
          write_puts(ctx, "= 0");
          break;
        case WASM_TYPE_F32:
          write_puts(ctx, "= $$fround(0)");
          break;
        case WASM_TYPE_F64:
          write_puts(ctx, "= 0.0");
          break;
        default:
          FAIL("invalid local type");
      }
      if (i != num_locals - 1)
        write_puts(ctx, ", ");
    }
    write_putc(ctx, ';');
    write_newline(ctx, WASM_TRUE);
  }
}

static void write_func(Context* ctx, size_t index) {
  const WasmFunc* func = ctx->module->funcs.data[index];
  ctx->current_func = func;
  wasm_make_type_binding_reverse_mapping(
      ctx->allocator, &func->decl.sig.param_types, &func->param_bindings,
      &ctx->param_index_to_name);
  wasm_make_type_binding_reverse_mapping(ctx->allocator, &func->local_types,
                                         &func->local_bindings,
                                         &ctx->local_index_to_name);

  writef(ctx, "function " PRIss "(", SS_ARG(func->name));
  write_param_list(ctx, func);
  write_puts(ctx, ") {");
  write_newline(ctx, WASM_TRUE);
  indent(ctx);
  write_param_type_annotations(ctx, func);
  write_locals(ctx, func);
  write_statement_list(ctx, func->first_expr);
  dedent(ctx);
  write_puts(ctx, "}");
  write_newline(ctx, WASM_TRUE);
  ctx->current_func = NULL;
}

static void write_table(Context* ctx, const WasmVarVector* vars) {
  size_t i;
  writef(ctx, "var $$TABLE = [");
  const WasmModule* module = ctx->module;
  for (i = 0; i < ctx->table_size; ++i) {
    if (i < vars->size) {
      const WasmFunc* func = wasm_get_func_by_var(module, &vars->data[i]);
      write_string_slice(ctx, &func->name, NEXT_CHAR_NONE);
    } else {
      write_puts(ctx, "$$bad");
    }
    if (i != ctx->table_size - 1)
      write_puts(ctx, ", ");
  }
  write_puts(ctx, "];");
  write_newline(ctx, WASM_TRUE);
}

static void write_import(Context* ctx, size_t index) {
  const WasmImport* import = ctx->module->imports.data[index];
  writef_nl(ctx, "var " PRIss " = ffi." PRIss "." PRIss ";",
            SS_ARG(import->name), SS_ARG(import->module_name),
            SS_ARG(import->func_name));
}

static void write_export(Context* ctx, size_t export_index) {
  const WasmExport* export = ctx->module->exports.data[export_index];
  size_t func_index =
      (size_t)wasm_get_func_index_by_var(ctx->module, &export->var);
  assert(func_index < ctx->module->funcs.size);
  const WasmFunc* func = ctx->module->funcs.data[func_index];
  writef_nl(ctx, PRIss ": " PRIss ",", SS_ARG(export->name),
            SS_ARG(func->name));
}

static void write_module(Context* ctx, const WasmModule* module) {
  size_t i;
  /* file header */
  writef_nl(ctx,
            "(function (global, ffi) {\n"
            "  var module = function(stdlib, ffi, mem) {\n"
            "    \"use asm\";");
  indent(ctx);
  indent(ctx);

  ctx->table_size = module->table ? next_power_of_two(module->table->size) : 0;

  /* imports */
  for (i = 0; i < module->imports.size; ++i)
    write_import(ctx, i);

  /* funcs */
  for (i = 0; i < module->funcs.size; ++i)
    write_func(ctx, i);

  /* table */
  if (module->table)
    write_table(ctx, module->table);

  /* exports */
  writef_nl(ctx, "return {");
  indent(ctx);
  for (i = 0; i < module->exports.size; ++i)
    write_export(ctx, i);
  dedent(ctx);
  writef_nl(ctx, "};");

  /* asm module footer */
  dedent(ctx);
  writef_nl(ctx, "};");

  /* memory */
  writef_nl(ctx, "var memory = new Uint8Array(%" PRIu64 ");",
            module->memory ? module->memory->max_pages * WASM_PAGE_SIZE : 0);

  writef_nl(ctx, "var instance = module(global, ffi, memory.buffer);");

  /* start */

  /* file footer */
  writef_nl(ctx, "return instance;");
  dedent(ctx);
  writef_nl(ctx, "})");

  /* force the newline to be written */
  write_next_char(ctx);
}

WasmResult wasm_write_asmjs(struct WasmAllocator* allocator,
                            struct WasmWriter* writer,
                            const struct WasmModule* module,
                            const WasmWriteAsmjsOptions* options) {
  Context ctx;
  WASM_ZERO_MEMORY(ctx);
  ctx.allocator = allocator;
  ctx.module = module;
  ctx.result = WASM_OK;
  wasm_init_stream(&ctx.stream, writer, NULL);
  write_module(&ctx, module);
  wasm_destroy_string_slice_vector(allocator, &ctx.param_index_to_name);
  wasm_destroy_string_slice_vector(allocator, &ctx.local_index_to_name);
  return ctx.result;
}
