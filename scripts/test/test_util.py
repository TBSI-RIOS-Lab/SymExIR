import sys

import regex as re

sys.path.append("..")

import util


def test_get_value_name():
    assert util.get_instr_value_name("%1 = call ..", "call") == "%1"
    assert util.get_instr_value_name("store %1", "store") == "NoValueName"


if __name__ == "__main__":
    test_get_value_name()
