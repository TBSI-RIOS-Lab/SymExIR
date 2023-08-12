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


def test_verify_simple_1():
    load_info = st.LoadAssertInfo(test_case_int_simple_1_l)
    v_info = st.VerificationLaodInfo(test_case_int_simple_1, load_info)
    verify.verify(v_info, load_info)


if __name__ == "__main__":
    test_verify_simple_1()
