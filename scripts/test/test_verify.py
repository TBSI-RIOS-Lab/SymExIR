import sys

import regex as re

sys.path.append("..")

import verify
import structure as st

test_case_int_simple_1 = [
    "%1 = load i32, i32* %5, align 8, !tbaa !4",
    "%6 = load i32, i32* %5, align 8, !tbaa !4",
    "%7 = add i32 %6, %1",
]

test_case_int_simple_1_info = [(0, "1"), (1, "1"), (2, "2")]

test_case_int_simple_2 = [
    "%1 = load i32, i32* %5, align 8, !tbaa !4",
    "%6 = load i32, i32* %5, align 8, !tbaa !4",
    "%7 = add i32 %6, %1",
    "%9 = load i32, i32* %8, align 8, !tbaa !4",
    "%10 = add i32 %9, %1",
    "%11 = mul i32 %10, %1",
]


test_case_int_simple_2_info = [
    (0, "1"),
    (1, "1"),
    (2, "2"),
    (3, "300"),
    (4, "301"),
    (5, "302"),
]


test_case_int_simple_3 = [
    "%1 = load i32, i32* %5, align 8, !tbaa !4",
    "%6 = load i32, i32* %5, align 8, !tbaa !4",
    "%7 = add i32 %6, %1",
    "%9 = load i32, i32* %8, align 8, !tbaa !4",
    "%10 = add i32 %9, %1",
    "%11 = mul i32 %10, %1",
    "%12 = udiv i32 %10, %1",
    "%13 = sub i32 %10, %1",
    "%14 = add i32 %10, %1",
    "%15 = urem i32 %10, %1",
    "%16 = icmp ne i32 %14, %15",
    "%17 = and i32 %12, %14",
    "%18 = or i32 %12, %14",
    "%19 = xor i32 4, %14",
    "%20 = xor i64 4, 1",
    "%21 = xor i32 4, 1",
    "%22 = xor i1 0, 1",
]


test_case_int_simple_3_info = [
    (0, "1"),
    (1, "1"),
    (2, "2"),
    (3, "300"),
    (4, "301"),
    (5, "301"),
    (6, "301"),
    (7, "300"),
    (8, "302"),
    (9, "0"),
    (10, "0"),
    (11, "300"),
    (12, "303"),
    (13, "298"),
    (14, "5"),
    (15, "5"),
    (16, "1"),
]


test_case_int_vector_1 = [
    "%1 = load <3 x i32>, <3 x i32>* %0, align 8",
    "%101 = load <3 x i32>, <3 x i32>* %0, align 8",
    "%2 = add <3 x i32> %1, < i32 1, i32 2, i32 2>",
    "%3 = sub <3 x i32> %101, < i32 1, i32 2, i32 2>",
]


test_case_int_vector_1_info = [
    (0, "< i32 1, i32 1, i32 1>"),
    (1, "< i32 1, i32 1, i32 1>"),
    (2, "< i32 2, i32 3, i32 3>"),
    (2, "< i32 0, i32 4294967295, i32 4294967295>"),
]


def test_verify_simple_1():
    load_info = st.LoadAssertInfo(test_case_int_simple_1_info)
    v_info = st.VerificationLaodInfo(test_case_int_simple_1, load_info)
    verify.verify(v_info, load_info)


def test_verify_simple_2():
    load_info = st.LoadAssertInfo(test_case_int_simple_2_info)
    v_info = st.VerificationLaodInfo(test_case_int_simple_2, load_info)
    try:
        verify.verify(v_info, load_info)
    except RuntimeError:
        pass
    else:
        assert False and "wrong exception!\n"


def test_verify_simple_3():
    load_info = st.LoadAssertInfo(test_case_int_simple_3_info)
    v_info = st.VerificationLaodInfo(test_case_int_simple_3, load_info)
    verify.verify(v_info, load_info)


def test_verify_int_vector_1():
    load_info = st.LoadAssertInfo(test_case_int_vector_1_info)
    v_info = st.VerificationLaodInfo(test_case_int_vector_1, load_info)
    # verify.verify(v_info, load_info, False) 


def test_calculate_simple_3():
    load_info = st.LoadAssertInfo(test_case_int_simple_3_info)
    v_info = st.VerificationLaodInfo(test_case_int_simple_3, load_info)
    verify.generate_calculate_result(v_info, load_info)


def test_calculate_int_vector_1():
    load_info = st.LoadAssertInfo(test_case_int_vector_1_info)
    v_info = st.VerificationLaodInfo(test_case_int_vector_1, load_info)
    verify.generate_calculate_result(v_info, load_info)


if __name__ == "__main__":
    test_verify_simple_1()
    test_verify_simple_2()
    test_verify_simple_3()
    test_verify_int_vector_1()
    test_calculate_simple_3()
    test_calculate_int_vector_1()
