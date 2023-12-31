import sys
from typing import List

import regex as re

sys.path.append("..")

import parse
import structure as st
import z3
import z3Extension as z3e
import util

test_case_float = [
    "%1 = load double, double* %5, align 8, !tbaa !4",
    "%6 = load double, double* %5, align 8, !tbaa !4",
    "%7 = fadd double %6, %1",
    "store double %7, double* %5, align 8, !tbaa !4",
    "%8 = getelementptr inbounds [1024 x double], [1024 x double]* @a, i64 0, i64 %4",
    "%9 = load double, double* %8, align 8, !tbaa !4",
    "%10 = fadd double %9, %1",
    "%11 = fmul double %10, %1",
    "store double %11, double* %8, align 8, !tbaa !4",
    "%12 = add nuw nsw i64 1, 1",
    "%13 = icmp eq i64 %12, 1024",
]


test_case_float_simple = [
    "%1 = load double, double* %5, align 8, !tbaa !4",
    "%6 = load double, double* %5, align 8, !tbaa !4",
    "%7 = fadd double %6, %1",
    "%9 = load double, double* %8, align 8, !tbaa !4",
    "%10 = fadd double %9, %1",
    "%11 = fmul double %10, %1",
    "%12 = fdiv double %10, %1",
    "%13 = fsub double %10, %1",
    "%14 = fadd double %10, %1",
    "%15 = frem double %10, %1",
    "%16 = fneg double %10",
    "%17 = fadd float 4.01, 4.02",
    "%18 = fadd double 4.01, 4.02",
]


test_case_int_simple = [
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


test_case_int_vector = [
    "%1 = load <3 x i32>, <3 x i32>* %0, align 8",
    "%101 = load <3 x i32>, <3 x i32>* %0, align 8",
    "%2 = add <3 x i32> %1, < i32 1, i32 2, i32 2>",
    "%3 = sub <3 x i32> %101, < i32 1, i32 2, i32 2>",
    "%4 = sub <3 x i32> < i32 1, i32 2, i32 2>, < i32 1, i32 2, i32 2>",
    "%5 = mul <3 x i32> %1, < i32 1, i32 2, i32 2>",
    "%6 = shl <3 x i32> %5, < i32 1, i32 2, i32 2>",
    "%7 = udiv <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%8 = sdiv <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%9 = and <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%10 = or <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%11 = xor <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%12 = lshr <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%13 = ashr <3 x i32> %6, < i32 1, i32 2, i32 2>",
    "%14 = icmp eq <3 x i32> < i32 1, i32 2, i32 7>, < i32 1, i32 2, i32 2>",
]


def test_slice_instr():
    test_case_1 = "%10 = add i64 %9, %6"
    re = parse.slice_instr(test_case_1, "i64", "%10")
    assert re.return_value_name == "%10"
    assert re.return_value_type == "i64"


def test_separate_argument():
    res = parse.separate_argument("<4 x i32> %a, <4 x i32> %b")
    res = parse.separate_argument(
        "<2 x i32> < i32 1, i32 2>, <2 x i32> < i32 1, i32 2>"
    )
    res = parse.separate_argument(
        "<2 x i32> %3, <2 x i32> %4"
    )
    res = parse.separate_argument(
        "<2 x i32> %3"
    )
    
def test_get_opcode():
    test_case_1 = "%10 = add i64 %9, %6"
    opcode = parse.get_opcode(test_case_1.split(",")[0])
    assert opcode == "add"

    test_case_2 = "catchswitch11"  # Yes, the check here is really simple.
    opcode = parse.get_opcode(test_case_2.split(",")[0])
    assert opcode == "unimplemented"


def test_regex_sample():
    test_case_fneg = "fneg float %val"
    test_case_fneg_v = "fneg <2 x float> %val"
    test_case_add_v = "add nuw <2 x i32> < i32 1, i32 1>, < i32 1, i32 2>"
    test_case_add = "add i32 4, %var"
    test_case_fadd = "fadd fast float %9, %6"
    test_case_fadd_v = (
        "fadd <2 x float> < float 1.0, float 1.0>, < float 1.0, float 1.0>"
    )
    test_case_sub = "sub nuw nsw i32 0, %val"
    test_case_sub_v = "sub nuw nsw <2 x i32> < i32 1, i32 1>, < i32 1, i32 2>"
    test_case_fsub = "fsub fast float 4.0, %var"
    test_case_mul = "mul i32 4, %var"
    test_case_fmul = "fmul fast float 4.0, %var"
    test_case_fmul_v = (
        "fmul <2 x float> < float 1.0, float 1.0>, < float 1.0, float 1.0>"
    )
    test_case_udiv = "udiv exact i32 4, %var"
    test_case_sdiv = "sdiv exact i32 4, %var"
    test_case_fdiv = "fdiv float 4.0, %var"
    test_case_fdiv_v = (
        "fdiv <2 x float> < float 1.0, float 1.0>, < float 1.0, float 1.0>"
    )
    test_case_urem = "urem i32 4, %var"
    test_case_srem = "srem i32 4, %var"
    test_case_frem = "frem float 4.0, %var"
    test_case_shl = "shl i32 4, %var"
    test_case_shl_v = "shl nuw <2 x i32> < i32 1, i32 1>, < i32 1, i32 2>"
    test_case_lshr = "lshr i32 1, 32"
    test_case_lshr_v = "lshr <2 x i32> < i32 -2, i32 4>, < i32 1, i32 2>"
    test_case_ashr_v = "ashr <2 x i32> < i32 -2, i32 4>, < i32 1, i32 3>"
    test_case_and = "and i32 4, %var"
    test_case_and_v = "and <2 x i32> < i32 -2, i32 4>, %var"
    test_case_or = "or i32 4, %var"
    test_case_xor = "xor i32 4, %var"
    test_case_extractelement = (
        "extractelement <4 x i32> < i32 8, i32 8, i32 8, i32 8>, i32 0"
    )
    test_case_extractelement_vscale = "extractelement <6 x 4 x i32> %vec, i32 0"
    test_case_insertelement = "insertelement <4 x i32> %vec, i32 1, i32 0"
    test_case_insertelement_vector = (
        "insertelement <4 x i32> < i32 8, i32 8, i32 8, i32 8>, i32 1, i32 0"
    )
    test_case_shufflevector = "shufflevector <4 x i32> %v1, <4 x i32> %v2, <4 x i32> <i32 0, i32 4, i32 1, i32 5>"
    test_case_trunc = "trunc i32 122 to i1"
    test_case_trunc_v = "trunc <3 x i16> <i16 8, i16 7, i16 8> to <3 x i8>"

    test_case_icmp = "icmp ne ptr %X, %X"
    test_case_fcmp = "fcmp one float 4.0, 5.0"
    test_case_select = "select <N x i1> <i1 true, i1 true>, <2 x i8> < i8 17, i8 42>, <2 x i8> < i8 17, i8 42>"  # This is not real instruction in LLVM.

    test_case_store = "store i32 3, ptr %ptr"
    test_case_store_float = "store double %7, double* %5, align 8, !tbaa !4"
    test_case_alloca = "alloca i32"
    test_case_alloca_align = "alloca i32, i32 4, align 1024"
    test_case_load = "load i32, ptr %ptr"
    test_case_load_v = "load <3 x i1>, <3 x i1>* %1, align 8"
    test_case_call_1 = "call i8 @llvm.smax.i8(i8 42, i8 -24)"
    test_case_call_2 = "call <4 x i32> @llvm.smax.v4i32(<4 x i32> %a, <4 x i32> %b)"
    test_case_getelementptr = (
        "getelementptr inbounds [1024 x double], [1024 x double]* @a, i64 0, i64 %4"
    )
    test_case_insertvalue = "insertvalue {i32, float} undef, i32 1, 0"
    test_case_extractvalue = "extractvalue {i32, float} %agg, 0"

    test_case_atomicrmw = "atomicrmw add ptr %ptr, i32 1 acquire"
    test_case_cmpxchg = "cmpxchg ptr %ptr, i32 %cmp, i32 %squared acq_rel monotonic"
    test_case_ptrtoint = "ptrtoint ptr %P to i8"
    test_case_ptrtoint_vector = (
        "ptrtoint <4 x ptr> < ptr 1, ptr 1, ptr 1, ptr 1> to <4 x i64>"
    )
    test_case_inttoptr = "inttoptr i32 255 to ptr"
    test_case_inttoptr_vector = (
        "inttoptr <4 x i32> < i32 1, i32 1, i32 1, i32 1> to <4 x ptr>"
    )
    test_case_bitcast = "bitcast i32* %x to i16*"
    test_case_bitcast_vec = "bitcast <2 x i32*> %V to <2 x i64*>"
    test_case_addrspacecast = "addrspacecast ptr %x to ptr addrspace(1)"
    test_case_addrspacecast_vec = "addrspacecast <4 x ptr> %z to <4 x ptr addrspace(3)>"

    gs: re.Match[str] | None = util.extra_slice_token(test_case_fneg, "fneg")
    assert gs is not None
    assert gs["type"] == "float"
    assert gs["op1"] == "%val"

    gs = util.extra_slice_token(test_case_fneg_v, "fneg")
    assert gs is not None
    assert gs["type"] == "<2 x float>"
    assert gs["op1"] == "%val"

    gs = util.extra_slice_token(test_case_add_v, "add")
    assert gs is not None
    assert gs["type"] == "<2 x i32>"
    assert gs["firstop"] == "< i32 1, i32 1>"

    gs = util.extra_slice_token(test_case_add, "add")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"

    gs = util.extra_slice_token(test_case_fadd, "fadd")
    assert gs is not None
    assert gs["type"] == "float"

    gs = util.extra_slice_token(test_case_fadd_v, "fadd")
    assert gs is not None
    assert gs["type"] == "<2 x float>"
    assert gs["firstop"] == "< float 1.0, float 1.0>"

    gs = util.extra_slice_token(test_case_sub, "sub")
    assert gs is not None
    assert gs["type"] == "i32"

    gs = util.extra_slice_token(test_case_sub_v, "sub")
    assert gs is not None
    assert gs["type"] == "<2 x i32>"
    assert gs["firstop"] == "< i32 1, i32 1>"

    gs = util.extra_slice_token(test_case_fsub, "fsub")
    assert gs is not None
    assert gs["type"] == "float"

    gs = util.extra_slice_token(test_case_mul, "mul")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_fmul, "fmul")
    assert gs is not None
    assert gs["type"] == "float"

    gs = util.extra_slice_token(test_case_fmul_v, "fmul")
    assert gs is not None
    assert gs["type"] == "<2 x float>"
    assert gs["firstop"] == "< float 1.0, float 1.0>"

    gs = util.extra_slice_token(test_case_udiv, "udiv")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_sdiv, "sdiv")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_fdiv, "fdiv")
    assert gs is not None
    assert gs["type"] == "float"
    assert gs["firstop"] == "4.0"

    gs = util.extra_slice_token(test_case_fdiv_v, "fdiv")
    assert gs is not None
    assert gs["type"] == "<2 x float>"
    assert gs["firstop"] == "< float 1.0, float 1.0>"

    gs = util.extra_slice_token(test_case_urem, "urem")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"

    gs = util.extra_slice_token(test_case_srem, "srem")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"

    gs = util.extra_slice_token(test_case_frem, "frem")
    assert gs is not None
    assert gs["type"] == "float"
    assert gs["firstop"] == "4.0"

    gs = util.extra_slice_token(test_case_shl, "shl")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"

    gs = util.extra_slice_token(test_case_shl_v, "shl")
    assert gs is not None
    assert gs["type"] == "<2 x i32>"
    assert gs["firstop"] == "< i32 1, i32 1>"

    gs = util.extra_slice_token(test_case_lshr, "lshr")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "1"
    assert gs["secondop"] == "32"

    gs = util.extra_slice_token(test_case_lshr_v, "lshr")
    assert gs is not None
    assert gs["type"] == "<2 x i32>"
    assert gs["firstop"] == "< i32 -2, i32 4>"
    assert gs["secondop"] == "< i32 1, i32 2>"

    gs = util.extra_slice_token(test_case_ashr_v, "ashr")
    assert gs is not None
    assert gs["type"] == "<2 x i32>"
    assert gs["firstop"] == "< i32 -2, i32 4>"
    assert gs["secondop"] == "< i32 1, i32 3>"

    gs = util.extra_slice_token(test_case_and, "and")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_and_v, "and")
    assert gs is not None
    assert gs["type"] == "<2 x i32>"
    assert gs["firstop"] == "< i32 -2, i32 4>"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_or, "or")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_xor, "xor")
    assert gs is not None
    assert gs["type"] == "i32"
    assert gs["firstop"] == "4"
    assert gs["secondop"] == "%var"

    gs = util.extra_slice_token(test_case_extractelement, "extractelement")
    assert gs is not None
    assert gs["vs"] == None
    assert gs["n"] == "4"
    assert gs["ty"] == "i32"
    assert gs["val"] == "< i32 8, i32 8, i32 8, i32 8>"
    assert gs["ty1"] == "i32"

    gs = util.extra_slice_token(test_case_extractelement_vscale, "extractelement")
    assert gs is not None
    assert gs["vs"] == "6"
    assert gs["n"] == "4"
    assert gs["ty"] == "i32"
    assert gs["ty1"] == "i32"

    gs = util.extra_slice_token(test_case_insertelement, "insertelement")
    assert gs is not None
    assert gs["n"] == "4"
    assert gs["ty"] == "i32"
    assert gs["ty1"] == "i32"
    assert gs["ty2"] == "i32"
    assert gs["val"] == "%vec"

    gs = util.extra_slice_token(test_case_insertelement_vector, "insertelement")
    assert gs is not None
    assert gs["n"] == "4"
    assert gs["ty"] == "i32"
    assert gs["ty1"] == "i32"
    assert gs["ty2"] == "i32"
    assert gs["val"] == "< i32 8, i32 8, i32 8, i32 8>"

    gs = util.extra_slice_token(test_case_shufflevector, "shufflevector")
    assert gs is not None
    assert gs["v1_vs"] == None
    assert gs["v1_ty"] == "i32"
    assert gs["v1"] == "%v1"
    assert gs["v2_vs"] == None
    assert gs["v2_ty"] == "i32"

    gs = util.extra_slice_token(test_case_trunc, "trunc")
    assert gs is not None
    assert gs["ty1"] == "i32"
    assert gs["val"] == "122"

    gs = util.extra_slice_token(test_case_trunc_v, "trunc")
    assert gs is not None
    assert gs["ty1"] == "<3 x i16>"
    assert gs["val"] == "<i16 8, i16 7, i16 8>"

    gs = util.extra_slice_token(test_case_icmp, "icmp")
    assert gs is not None
    assert gs["cond"] == "ne"
    assert gs["ty"] == "ptr"
    assert gs["op1"] == "%X"

    gs = util.extra_slice_token(test_case_fcmp, "fcmp")
    assert gs is not None
    assert gs["cond"] == "one"
    assert gs["ty"] == "float"
    assert gs["op1"] == "4.0"

    gs = util.extra_slice_token(test_case_select, "select")
    assert gs is not None
    assert gs["selty"] == "<N x i1>"
    assert gs["cond"] == "<i1 true, i1 true>"
    assert gs["ty1"] == "<2 x i8>"
    assert gs["op1"] == "< i8 17, i8 42>"
    assert gs["ty2"] == "<2 x i8>"
    assert gs["op2"] == "< i8 17, i8 42>"

    gs = util.extra_slice_token(test_case_store, "store")
    assert gs is not None
    assert gs["ty"] == "i32"
    assert gs["value"] == "3"
    assert gs["ptr_ty"] == "ptr"
    assert gs["pointer"] == "%ptr"

    gs = util.extra_slice_token(test_case_store_float, "store")
    assert gs is not None
    assert gs["ty"] == "double"
    assert gs["value"] == "%7"
    assert gs["ptr_ty"] == "double*"
    assert gs["pointer"] == "%5"

    gs = util.extra_slice_token(test_case_alloca, "alloca")
    assert gs is not None
    assert gs["ty"] == "i32"
    assert gs["align"] == None

    gs = util.extra_slice_token(test_case_alloca_align, "alloca")
    assert gs is not None
    assert gs["ty"] == "i32"
    assert gs["align"] == "1024"

    gs = util.extra_slice_token(test_case_load, "load")
    assert gs is not None
    assert gs["ty"] == "i32"

    gs = util.extra_slice_token(test_case_load_v, "load")
    assert gs is not None
    assert gs["ty"] == "<3 x i1>"

    gs = util.extra_slice_token(test_case_call_1, "call")
    assert gs is not None
    assert gs["ty"] == "i8"

    gs = util.extra_slice_token(test_case_call_2, "call")
    assert gs is not None
    assert gs["ty"] == "<4 x i32>"
    assert gs["function"] == "@llvm.smax.v4i32(<4 x i32> %a, <4 x i32> %b)"

    gs = util.extra_slice_token(test_case_getelementptr, "getelementptr")
    assert len(gs.group()) == 0

    gs = util.extra_slice_token(test_case_insertvalue, "insertvalue")
    assert gs is not None
    assert gs["type"] == "{i32, float}"
    assert gs["op_val"] == "undef"
    assert gs["idx"] == "i32 1, 0"

    gs = util.extra_slice_token(test_case_extractvalue, "extractvalue")
    assert gs is not None
    assert gs["type"] == "{i32, float}"
    assert gs["op_val"] == "%agg"
    assert gs["idx"] == "0"

    gs = util.extra_slice_token(test_case_atomicrmw, "atomicrmw")
    assert gs is not None
    assert gs["ty"] == "i32"

    gs = util.extra_slice_token(test_case_cmpxchg, "cmpxchg")
    assert gs is not None
    assert gs["ty"] == "i32"

    gs = util.extra_slice_token(test_case_ptrtoint, "ptrtoint")
    assert gs is not None
    assert gs["ptr_ty"] == "ptr"
    assert gs["ty"] == "i8"

    gs = util.extra_slice_token(test_case_ptrtoint_vector, "ptrtoint")
    assert gs is not None
    assert gs["ptr_val"] == "< ptr 1, ptr 1, ptr 1, ptr 1>"
    assert gs["ty"] == "<4 x i64>"

    gs = util.extra_slice_token(test_case_inttoptr, "inttoptr")
    assert gs is not None
    assert gs["ty"] == "i32"
    assert gs["val"] == "255"
    assert gs["ptr_ty"] == "ptr"

    gs = util.extra_slice_token(test_case_inttoptr_vector, "inttoptr")
    assert gs is not None
    assert gs["ty"] == "<4 x i32>"
    assert gs["val"] == "< i32 1, i32 1, i32 1, i32 1>"
    assert gs["ptr_ty"] == "<4 x ptr>"

    gs = util.extra_slice_token(test_case_bitcast, "bitcast")
    assert gs is not None
    assert gs["ty"] == "i16*"
    assert gs["val"] == "%x"
    assert gs["ptr_ty"] == "i32*"

    gs = util.extra_slice_token(test_case_bitcast_vec, "bitcast")
    assert gs is not None
    assert gs["ty"] == "<2 x i64*>"
    assert gs["val"] == "%V"
    assert gs["ptr_ty"] == "<2 x i32*>"

    gs = util.extra_slice_token(test_case_addrspacecast, "addrspacecast")
    assert gs is not None
    assert gs["ptr_ty"] == "ptr"

    gs = util.extra_slice_token(test_case_addrspacecast_vec, "addrspacecast")
    assert gs is not None
    assert gs["ptr_ty"] == "<4 x ptr>"


def test_get_smt_vector():
    value_name = "%1"
    vec_type = "<2 x i32>"
    X = parse.get_smt_vector(value_name, vec_type)
    assert isinstance(X[0], z3.z3.BitVecRef)


def test_get_smt_val_vector():
    value_name = "< i32 1, i32 1>"
    vec_type = "<2 x i32>"
    res = parse.get_smt_val_vector(value_name, vec_type)
    assert isinstance(res[0], z3.BitVecNumRef)
    value_name = "< float 1.0, float 1.0>"
    vec_type = "<2 x float>"
    res = parse.get_smt_val_vector(value_name, vec_type)
    assert isinstance(res[0], z3.z3.FPNumRef)


def test_generate_instr_types():
    result = parse.generate_instr_types(test_case_float)
    assert result[0] == "load"


def test_get_type_precision():
    assert parse.get_type_precision("i64") == 64


def test_parse_float():
    smt = st.VerificationContext()
    parse.parse_instr_basic(test_case_float_simple[0], "load", smt)
    parse.parse_instr_basic(test_case_float_simple[1], "load", smt)
    parse.parse_instr_basic(test_case_float_simple[2], "fadd", smt)
    parse.parse_instr_basic(test_case_float_simple[3], "load", smt)
    parse.parse_instr_basic(test_case_float_simple[4], "fadd", smt)
    parse.parse_instr_basic(test_case_float_simple[5], "fmul", smt)
    parse.parse_instr_basic(test_case_float_simple[6], "fdiv", smt)
    parse.parse_instr_basic(test_case_float_simple[7], "fsub", smt)
    parse.parse_instr_basic(test_case_float_simple[8], "fadd", smt)
    parse.parse_instr_basic(test_case_float_simple[9], "frem", smt)
    parse.parse_instr_basic(test_case_float_simple[10], "fneg", smt)
    parse.parse_instr_basic(test_case_float_simple[11], "fadd", smt)
    parse.parse_instr_basic(test_case_float_simple[12], "fadd", smt)
    # smt.dump()


def test_parse_int():
    smt = st.VerificationContext()
    parse.parse_instr_basic(test_case_int_simple[0], "load", smt)
    parse.parse_instr_basic(test_case_int_simple[1], "load", smt)
    parse.parse_instr_basic(test_case_int_simple[2], "add", smt)
    parse.parse_instr_basic(test_case_int_simple[3], "load", smt)
    parse.parse_instr_basic(test_case_int_simple[4], "add", smt)
    parse.parse_instr_basic(test_case_int_simple[5], "mul", smt)
    parse.parse_instr_basic(test_case_int_simple[6], "udiv", smt)
    parse.parse_instr_basic(test_case_int_simple[7], "sub", smt)
    parse.parse_instr_basic(test_case_int_simple[8], "add", smt)
    parse.parse_instr_basic(test_case_int_simple[9], "urem", smt)
    parse.parse_instr_basic(test_case_int_simple[10], "icmp", smt)
    parse.parse_instr_basic(test_case_int_simple[11], "and", smt)
    parse.parse_instr_basic(test_case_int_simple[12], "or", smt)
    parse.parse_instr_basic(test_case_int_simple[13], "xor", smt)
    parse.parse_instr_basic(test_case_int_simple[14], "xor", smt)
    # smt.dump()


def test_parse_vector_int():
    smt = st.VerificationContext()
    parse.parse_instr(test_case_int_vector[0], "load", smt)
    parse.parse_instr(test_case_int_vector[1], "load", smt)
    parse.parse_instr(test_case_int_vector[2], "add", smt)
    parse.parse_instr(test_case_int_vector[3], "sub", smt)
    parse.parse_instr(test_case_int_vector[4], "sub", smt)
    parse.parse_instr(test_case_int_vector[5], "mul", smt)
    parse.parse_instr(test_case_int_vector[6], "shl", smt)
    parse.parse_instr(test_case_int_vector[7], "udiv", smt)
    parse.parse_instr(test_case_int_vector[8], "sdiv", smt)
    parse.parse_instr(test_case_int_vector[9], "and", smt)
    parse.parse_instr(test_case_int_vector[10], "or", smt)
    parse.parse_instr(test_case_int_vector[11], "xor", smt)
    parse.parse_instr(test_case_int_vector[12], "lshr", smt)
    parse.parse_instr(test_case_int_vector[13], "ashr", smt)
    parse.parse_instr(test_case_int_vector[14], "icmp", smt)
    # smt.dump()


def test_get_nn_basedOn_type():
    res = parse.get_nn_basedOn_type("i32", "32", False)
    assert str(res) == "32"
    res = parse.get_nn_basedOn_type("i1", "1", False)
    assert str(res) == "1"

    res = parse.get_nn_basedOn_type("bfloat", "2.233", False)
    assert str(res) == "1.1162109375*(2**1)"

    res = parse.get_nn_basedOn_type("double", "2.233", False)
    assert str(res) == "1.1165000000000000479616346638067625463008880615234375*(2**1)"


def test_get_nn_basedOn_type_v():
    res = parse.get_nn_basedOn_type("<2 x i32>", "< i32 1, i32 1>", True)
    assert isinstance(res, List)
    assert isinstance(res[0], z3.z3.BitVecNumRef)
    assert str(res[1]) == "1"


def test_get_info_from_vector():
    x1, x2 = parse.get_info_from_vector_type("<4 x i32>")
    assert x1 == 4
    assert x2 == "i32"
    x1, x2 = parse.get_info_from_vector_type("<4 x float>")
    assert x2 == "float"


def test_is_vector_type_basedon_dict_token():
    X = {
        "vs": None,
        "n": "4",
        "ty": "i32",
        "v1": "%v1",
        "v2": "%v2",
        "v3": "< i32 0, i32 4, i32 1, i32 5>",
    }
    assert parse.is_vectortype_basedon_dict_token(X, "", "") is False


def test_parse_instr_llvm_abs():
    smt = st.VerificationContext()
    parse.parse_instr_llvm_abs("%1", "<2 x i32> < i32 1, i32 1>", "<2 x i32>", smt)
    parse.parse_instr_llvm_abs("%2", "i32 1", "2", smt)
    # smt.dump()


def test_get_ready_two_value_v():
    smt = st.VerificationContext()
    res, _ = parse.get_two_value("< i32 1, i32 1>", "< i32 1, i32 1>", smt, "<2 x i32>")


def test_parse_instr_two_op_function_v():
    smt = st.VerificationContext()
    dict = {
        "firstop": "< i32 1, i32 1>",
        "secondop": "< i32 1, i32 1>",
        "type": "<2 x i32>",
    }
    parse.parse_instr_two_op_function_v("%10", dict, smt, z3e.BitVecAdd)
    # smt.dump()


def test_parse_instr_vector():
    smt = st.VerificationContext()
    test_case_vector_float = [
        "%1 = fadd <2 x float> < float 1.0, float 1.0>, < float 1.0, float 1.0>",
    ]
    parse.parse_instr(test_case_vector_float[0], "fadd", smt)


def test_parse_instr_call():
    smt = st.VerificationContext()
    test_case = [
        "%1 = call i8 @llvm.smax.i8(i8 42, i8 -24)",
        "%2 = call i8 @llvm.smin.i8(i8 42, i8 -24)",
        "%3 = call i8 @llvm.umax.i8(i8 42, i8 -24)",
        "%4 = call i8 @llvm.umin.i8(i8 42, i8 -24)",
        "%5 = call float @llvm.sin.f32(float 2.33)",
        "%6 = call float @llvm.cos.f32(float %5)",
        "%7 = call float @llvm.exp.f32(float %5)",
        "%8 = call float @llvm.exp2.f32(float %5)",
        "%9 = call float @llvm.exp2.f32(float %8)",
        "%10 = call float @llvm.log10.f32(float %8)",
        "%11 = call float @llvm.log2.f32(float 23)",
        "%12 = call float @llvm.trunc.f32(float 2.33)",
        "%13 = call float @llvm.floor.f32(float 2.33)",
        "%14 = call float @llvm.ceil.f32(float 2.33)",
    ]
    for i in range(len(test_case)):
        parse.parse_instr(test_case[i], "call", smt)
    smt.print_normal_float()


def test_parse_instr_vector_type():
    smt = st.VerificationContext()
    add_value = parse.get_nn_basedOn_type(
        "<4 x float>", "< float 2.011, float 2.0, float 3.0, float 4.0>", True
    )
    smt.add_new_value("%vec", add_value, "<4 x float>")
    instr_1 = "%1 = extractelement <4 x float> %vec, i32 0"
    instr_2 = "%2 = insertelement <4 x float> < float 3.01, float 2.0, float 3.0, float 4.0>, float 1, i32 0 "
    parse.parse_instr(instr_1, "extractelement", smt)
    parse.parse_instr(instr_2, "insertelement", smt)
    # smt.dump_with_value_name()


def test_parse_instr_select():
    smt = st.VerificationContext()
    test_instr_1 = "%1 = select <2 x i1> <i1 true, i1 false>, <2 x i8> < i8 1, i8 1>, <2 x i8> < i8 2, i8 2>"
    test_instr_2 = "%2 = select i1 true, i8 1, i8 2"
    parse.parse_instr(test_instr_1, "select", smt)
    parse.parse_instr(test_instr_2, "select", smt)
    # smt.dump_with_value_name()


def test_parse_instr_shufflevector():
    smt = st.VerificationContext()
    instr_1 = "%1 = shufflevector <2 x i32> < i32 1, i32 2>, <2 x i32> < i32 3, i32 4>, <3 x i32> <i32 0, i32 1, i32 2>"
    instr_2 = "%2 = shufflevector <2 x i32> < i32 1, i32 2>, <2 x i32> < i32 3, i32 4>, <3 x i32> <i32 3, i32 1, i32 2>"
    data_token = parse.get_instr_dict(
        instr_1,
        "shufflevector",
    )
    parse.parse_instr_shufflevector(instr_1, smt, data_token)
    parse.parse_instr(instr_2, "shufflevector", smt)
    # smt.dump()


def test_parse_aggregate_operations():
    smt = st.VerificationContext()
    instr_1 = "%1 = extractvalue {i32, float} %agg, 0"
    instr_2 = "%agg1 = insertvalue {i32, float} undef, i32 1, 0"
    instr_3 = "%agg2 = insertvalue {i32, float} %agg1, float %val, 1 "
    parse.parse_instr(instr_1, "extractvalue", smt)
    parse.parse_instr(instr_2, "insertvalue", smt)
    parse.parse_instr(instr_3, "insertvalue", smt)
    # smt.dump_with_type()


def test_parse_instr_mem():
    instr_1 = "%old = atomicrmw add ptr %ptr, i32 1 acquire"
    instr_2 = (
        "%val_success = cmpxchg ptr %ptr, i32 %cmp, i32 %squared acq_rel monotonic"
    )

    smt = st.VerificationContext()
    parse.parse_instr(instr_1, "atomicrmw", smt)
    parse.parse_instr(instr_2, "cmpxchg", smt)
    # smt.dump()


def test_parse_instr_ptrInvolved():
    instr_1 = "%pt_1 = ptrtoint ptr 677 to i8"
    instr_2 = "%pt_2 = ptrtoint <4 x ptr> <ptr 1, ptr 1, ptr 1, ptr 1> to <4 x i64>"
    instr_3 = "%ip_1 = inttoptr i32 255 to ptr"
    instr_4 = (
        "%ip_2 = inttoptr <4 x i32> <i32 99, i32 1, i32 100, i32 393> to <4 x ptr>"
    )
    instr_5 = "%b_1 = bitcast <2 x i32*> %V to <2 x i64*>"
    instr_6 = "%b_2 = bitcast <2 x i32*> %V to <2 x i64*>"
    instr_7 = "%X = addrspacecast ptr %x to ptr addrspace(1)"
    instr_8 = "%Z = addrspacecast <4 x ptr> %z to <4 x ptr addrspace(3)>"
    smt = st.VerificationContext()
    parse.parse_instr(instr_1, "ptrtoint", smt)
    parse.parse_instr(instr_2, "ptrtoint", smt)
    parse.parse_instr(instr_3, "inttoptr", smt)
    parse.parse_instr(instr_4, "inttoptr", smt)
    parse.parse_instr(instr_5, "bitcast", smt)
    parse.parse_instr(instr_6, "bitcast", smt)
    parse.parse_instr(instr_7, "addrspacecast", smt)
    parse.parse_instr(instr_8, "addrspacecast", smt)
    # smt.dump()


def test_whole_proccess_1():
    smt = st.VerificationContext()
    instr_types = parse.generate_instr_types(test_case_float)
    parse.parse_instrs(test_case_float, instr_types, smt)
    # smt.dump()


if __name__ == "__main__":
    test_slice_instr()
    test_get_opcode()
    test_separate_argument()
    test_parse_instr_llvm_abs()
    test_regex_sample()
    test_generate_instr_types()
    test_get_type_precision()
    test_parse_float()
    test_parse_int()
    test_get_nn_basedOn_type()
    test_get_info_from_vector()
    test_get_smt_val_vector()
    test_is_vector_type_basedon_dict_token()
    test_get_ready_two_value_v()
    test_get_smt_vector()
    test_parse_instr_shufflevector()
    test_parse_aggregate_operations()
    test_get_nn_basedOn_type_v()
    test_parse_instr_two_op_function_v()
    test_parse_instr_vector()
    test_parse_vector_int()
    test_parse_instr_call()
    test_whole_proccess_1()
    test_parse_instr_vector_type()
    test_parse_instr_select()
    test_parse_instr_mem()
    test_parse_instr_ptrInvolved()
    for line in test_case_float_simple:
        print(line)
