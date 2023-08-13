import argparse

import llvmlite.binding as llvm
import structure as st
import z3


def load_instructions(lines) -> list[int]:
    return []


def solver_check():
    pass


def proccess_inter():
    pass


def get_smt_sort(input_type):
    return z3.Float128()
    raise NotImplementedError(f"get_smt_sort {type.__class__}")


def testvalue():
    return 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--testfiles", type=str, help="The dir store the testcases.")
