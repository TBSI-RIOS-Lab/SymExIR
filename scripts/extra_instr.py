from __future__ import print_function

import argparse
import os
from typing import List

import llvmlite.binding as llvm


def find_all_ir_file(dir: str):
    for root, _, fs in os.walk(dir):
        for f in fs:
            if f.endswith(".ll"):
                yield os.path.join(root, f)


def extract_llvm_ir_commands(ll_file) -> List[llvm.value.ValueRef]:
    with open(ll_file, "r+") as irfile:
        irContent = irfile.read()
    # Load the ll file into an LLVM IR module.
    try:
        module = llvm.parse_assembly(irContent)
        module.verify()
    except RuntimeError:
        print("parse ir file fail, the file name is" + ll_file)
        return []
    # Get the list of all of the functions in the module.
    functions = module.functions
    # Iterate over the functions and extract the LLVM IR commands.
    llvm_ir_commands = []
    for function in functions:
        for block in function.blocks:
            for ins in block.instructions:
                llvm_ir_commands.append(ins)
    return llvm_ir_commands


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--testfiles", type=str, help="The dir store the testcases.")
    args = parser.parse_args()
    llvm_ir_commands = []
    for ll_file in find_all_ir_file(args.testfiles):
        print(ll_file)
        for commands in extract_llvm_ir_commands(ll_file):
            llvm_ir_commands.append(commands)
    llvm_ir_opcodes = set()
    for llvm_ir_command in llvm_ir_commands:
        llvm_ir_opcodes.add(llvm_ir_command.opcode)
    print(llvm_ir_opcodes)
