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
  parser.add_argument('-e', '--executable', metavar='PATH',
                      help='override sexpr-wasm executable.')
  parser.add_argument('--wasm-asmjs-executable', metavar='PATH',
                      help='override wasm-asmjs executable.')
  parser.add_argument('-v', '--verbose', help='print more diagnotic messages.',
                      action='store_true')
  parser.add_argument('--no-error-cmdline',
                      help='don\'t display the subprocess\'s commandline when' +
                          ' an error occurs', dest='error_cmdline',
                      action='store_false')
  parser.add_argument('--use-libc-allocator', action='store_true')
  parser.add_argument('--debug-names', action='store_true')
  parser.add_argument('file', help='test file.')
  options = parser.parse_args(args)

  sexpr_wasm = utils.Executable(
      find_exe.GetSexprWasmExecutable(options.executable),
      error_cmdline=options.error_cmdline)
  sexpr_wasm.AppendOptionalArgs({
    '-v': options.verbose,
    '--use-libc-allocator': options.use_libc_allocator,
    '--debug-names': options.debug_names
  })

  wasm_asmjs = utils.Executable(find_exe.GetWasmAsmjsExecutable(
      options.wasm_asmjs_executable),
      error_cmdline=options.error_cmdline)
  wasm_asmjs.AppendOptionalArgs({
    '--use-libc-allocator': options.use_libc_allocator,
    '--debug-names': options.debug_names
  })

  with utils.TempDirectory(options.out_dir, 'run-asmjs-') as out_dir:
    out_file = utils.ChangeDir(utils.ChangeExt(options.file, '.wasm'), out_dir)
    sexpr_wasm.RunWithArgs(options.file, '-o', out_file)
    wasm_asmjs.RunWithArgs(out_file)

  return 0


if __name__ == '__main__':
  try:
    sys.exit(main(sys.argv[1:]))
  except Error as e:
    sys.stderr.write(str(e) + '\n')
    sys.exit(1)

