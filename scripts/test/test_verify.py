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

test_case_int_simple_1_l = [(0, "1"), (1, "1"), (2, "2")]

test_case_int_simple_2 = [
    "%1 = load i32, i32* %5, align 8, !tbaa !4",
    "%6 = load i32, i32* %5, align 8, !tbaa !4",
    "%7 = add i32 %6, %1",
    "%9 = load i32, i32* %8, align 8, !tbaa !4",
    "%10 = add i32 %9, %1",
    "%11 = mul i32 %10, %1",
]

test_case_int_simple_1_2 = [
    (0, "1"),
    (1, "1"),
    (2, "2"),
    (3, "300"),
    (4, "301"),
    (5, "302"),
]


def test_verify_simple_1():
    load_info = st.LoadAssertInfo(test_case_int_simple_1_l)
    v_info = st.VerificationLaodInfo(test_case_int_simple_1, load_info)
    verify.verify(v_info, load_info)


def test_verify_simple_2():
    load_info = st.LoadAssertInfo(test_case_int_simple_1_2)
    v_info = st.VerificationLaodInfo(test_case_int_simple_2, load_info)
    try:
        verify.verify(v_info, load_info)
    except RuntimeError:
        print("Catch error")


if __name__ == "__main__":
    test_verify_simple_1()
    test_verify_simple_2()
