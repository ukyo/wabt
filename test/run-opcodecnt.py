#!/usr/bin/env python
#
# Copyright 2016 WebAssembly Community Group participants
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

import argparse
import os
import subprocess
import sys

import find_exe
import utils
from utils import Error

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def main(args):
  parser = argparse.ArgumentParser()
  parser.add_argument('-o', '--out-dir', metavar='PATH',
                      help='output directory for files.')
  parser.add_argument('--wast2wasm-executable', metavar='PATH',
                      help='override wast2wasm executable.')
  parser.add_argument('--wasmopcodecnt-executable', metavar='PATH',
                      help='override wasmopcodecnt executable.')
  parser.add_argument('-v', '--verbose', help='print more diagnotic messages.',
                      action='store_true')
  parser.add_argument('--no-error-cmdline',
                      help='don\'t display the subprocess\'s commandline when' +
                          ' an error occurs', dest='error_cmdline',
                      action='store_false')
  parser.add_argument('--print-cmd', help='print the commands that are run.',
                      action='store_true')
  parser.add_argument('--use-libc-allocator', action='store_true')
  parser.add_argument('file', help='test file.')
  options = parser.parse_args(args)

  wast2wasm = utils.Executable(
      find_exe.GetWast2WasmExecutable(options.wast2wasm_executable),
      error_cmdline=options.error_cmdline)
  wast2wasm.AppendOptionalArgs({
    '-v': options.verbose,
    '--use-libc-allocator': options.use_libc_allocator
  })

  wasmopcodecnt = utils.Executable(find_exe.GetWasmOpcodeCntExecutable(
      options.wasmopcodecnt_executable),
      error_cmdline=options.error_cmdline)
  wasmopcodecnt.AppendOptionalArgs({
    '--use-libc-allocator': options.use_libc_allocator
  })

  wast2wasm.verbose = options.print_cmd
  wasmopcodecnt.verbose = options.print_cmd

  with utils.TempDirectory(options.out_dir, 'run-opcodecnt-') as out_dir:
    out_file = utils.ChangeDir(utils.ChangeExt(options.file, '.wasm'), out_dir)
    wast2wasm.RunWithArgs(options.file, '-o', out_file)
    wasmopcodecnt.RunWithArgs(out_file)

  return 0


if __name__ == '__main__':
  try:
    sys.exit(main(sys.argv[1:]))
  except Error as e:
    sys.stderr.write(str(e) + '\n')
    sys.exit(1)


