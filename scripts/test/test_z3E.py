import sys

import z3

sys.path.append("..")

import parse
import z3Extension as z3e


def test_BvVector():
    sort = parse.get_basic_smt_sort("i32")
    a = z3e.BvVector("p", 4, sort)
    print(a)
    assert isinstance(a[2], z3.BitVecRef)


def test_BitvalVector():
    sort = parse.get_basic_smt_sort("i32")
    values = [1, 2, 3, 5]
    a = z3e.BitvalVector(values, sort)
    assert isinstance(a[2], z3.BitVecNumRef)
    assert a[1].as_string() == "2"
    assert a[3].as_string() == "5"


def test_FpVector():
    sort = parse.get_basic_smt_sort("float")
    X = z3e.FpVector("x", 5, sort)
    print(X)


def test_FpValVector():
    sort = parse.get_basic_smt_sort("float")
    values = [1.2, 2.2222, 4.32333]
    print(values)
    X = z3e.FpValVector(values, sort)
    print(X)


def test_op_on_vectors():
    sort = parse.get_basic_smt_sort("float")
    X = z3e.FpVector("x", 5, sort)
    Y = z3e.FpVector("x", 5, sort)
    rm = z3.RNE()
    res = [z3.simplify(z3e.fpAdd_RNE(X[i], Y[i])) for i in range(len(X))]


if __name__ == "__main__":
    test_BvVector()
    test_BitvalVector()
    test_FpVector()
    test_FpValVector()
    test_op_on_vectors()
