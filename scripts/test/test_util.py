import sys

import regex as re
import z3

sys.path.append("..")

import util
import utilComputeFunc as uf


def test_get_value_name():
    assert util.get_instr_value_name("%1 = call ..", "call") == "%1"
    assert util.get_instr_value_name("store %1", "store") == "NoValueName"


def test_get_vector_inner_type():
    assert util.get_vector_inner_type("<3 x i32>") == "i32"
    assert util.get_vector_inner_type("<3 x float>") == "float"
    assert util.get_vector_inner_type("<2 x 3 x float>") == "float"


def test_uf():
    s = uf.get_sin_result_single(z3.FPVal(20.0, z3.FPSort(8, 24)))
    print(s)
    uf.get_log2_result(z3.FPVal(20.0, z3.FPSort(8, 24)))

def test_is_vec_smt_type():
    assert util.is_vec_smt_type("<3 x i32>") is True


def test_pretty_smt_list():
    res_list = ["123", "3244", "999"]
    res = util.pretty_smt_list("<3 x i32>", res_list)
    print(res)

if __name__ == "__main__":
    # test_get_value_name()
    # test_get_vector_inner_type()
    # test_uf()
    # test_is_vec_smt_type()
    test_pretty_smt_list()
