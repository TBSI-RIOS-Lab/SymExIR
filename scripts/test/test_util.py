import sys

import regex as re

sys.path.append("..")

import util


def test_get_value_name():
    assert util.get_instr_value_name("%1 = call ..", "call") == "%1"
    assert util.get_instr_value_name("store %1", "store") == "NoValueName"


def test_get_vector_inner_type():
    assert util.get_vector_inner_type("<3 x i32>") == "i32"
    assert util.get_vector_inner_type("<3 x float>") == "float"
    assert util.get_vector_inner_type("<2 x 3 x float>") == "float"


if __name__ == "__main__":
    test_get_value_name()
    test_get_vector_inner_type()
