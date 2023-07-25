from typing import List

import z3 as smts

debug = False
defult_float_rm = smts.RNE()


def Bool2BitVector1(expr):
    if smts.is_true(expr) == True:
        return smts.BitVecVal(1, 1)
    else:
        return smts.BitVecVal(0, 1)


def check_is_bitvector_one(one):
    if not isinstance(one, smts.BitVecRef):
        raise TypeError("The input({}) is not z3.BitVecRef.".format(one.sort()))


def check_is_bitvector(first, second):
    check_is_bitvector_one(first)
    check_is_bitvector_one(second)


def BitVecSGT(a, b):
    return a > b


def BitVecAnd(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first & second


def BitVecOr(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first | second


def BitVecXor(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first ^ second


def BitVecAshr(first, second):
    return first >> second


def BitVecAdd(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first + second


def BitVecSub(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first - second


def BitVecMul(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first * second


def BitVecShl(first, second):
    return first << second


def BitVecSdiv(first, second):
    if debug:
        check_is_bitvector(first, second)
    return first / second


def BvVector(prefix: str, sz: int, bv_sort: smts.SortRef, ctx=None):
    """Return a list of BitVector constants of size 'sz'.

    >>> sort = parse.get_basic_smt_sort("i32")
    >>> X = z3e.BvVector("p", 100, sort)
    >>> X
    [p__0, p__1, p__2, p__3]
    """
    if not smts.is_bv_sort(bv_sort):
        raise Exception("The input sort({}) is not bv!\n".format(bv_sort))
    ctx = smts.get_ctx(ctx)

    return [smts.BitVec("%s__%s" % (prefix, i), bv_sort, ctx) for i in range(sz)]


def BitvalVector(values: List[int], bv_sort: smts.SortRef, ctx=None):
    """Return a list of bit-vector values with the given numbers.

    >>> sort = parse.get_basic_smt_sort("i32")
    >>> X = z3e.BvVector("p", 100, sort)
    >>> X
    [p__0, p__1, p__2, p__3]
    """
    if not smts.is_bv_sort(bv_sort):
        raise Exception("The input sort({}) is not bv!\n".format(bv_sort))
    ctx = smts.get_ctx(ctx)

    return [smts.BitVecVal(values[i], bv_sort, ctx) for i in range(len(values))]


def BitvalVector_dump_sort(v: List[smts.BitVecNumRef]):
    for member in v:
        print(member.sort())


def FpVector(prefix: str, sz: int, fp_sort: smts.SortRef, ctx=None):
    """Return a list of fp constants of size 'sz'.

    >>> sort = parse.get_basic_smt_sort("float")
    >>> X = z3e.FpVector("x", 5, sort)
    >>> X
    [x__0, x__1, x__2, x__3, x__4]
    """
    if not smts.is_fp_sort(fp_sort):
        raise Exception("The input sort({}) is not fp!\n".format(fp_sort))
    ctx = smts.get_ctx(ctx)

    return [smts.FP("%s__%s" % (prefix, i), fp_sort, ctx) for i in range(sz)]


def FpValVector(values: List[float], fp_sort: smts.SortRef, ctx=None):
    """Return a list of fp val from the values. The sort of fpvals is based on the fp_sort.
    If `ctx=None`, then the global context is used.

    >>> sort = parse.get_basic_smt_sort("float")
    >>> values = [1.2, 2.2222, 4.32333]
    >>> X = FpValVector(values, sort)
    [1.2000000476837158203125, 1.1110999584197998046875*(2**1), 1.08083248138427734375*(2**2)]
    """
    if not smts.is_fp_sort(fp_sort):
        raise Exception("The input sort({}) is not fp!\n".format(fp_sort))
    ctx = smts.get_ctx(ctx)

    return [smts.FPVal(values[i], fp_sort, ctx) for i in range(len(values))]


def fpAdd_RNE(a, b, ctx=None):
    return smts.fpAdd(defult_float_rm, a, b, ctx)


def fpMul_RNE(a, b, ctx=None):
    return smts.fpMul(defult_float_rm, a, b, ctx)


def fpSub_RNE(a, b, ctx=None):
    return smts.fpSub(defult_float_rm, a, b, ctx)


def fpDiv_RNE(a, b, ctx=None):
    return smts.fpDiv(defult_float_rm, a, b, ctx)


def fpFPToFP_RNE(v, sort, ctx=None):
    return smts.fpFPToFP(smts.RNE(), v, sort, ctx)


def fpToUBV_RTZ(a, b, ctx=None):
    return smts.fpToUBV(smts.RTZ(), a, b, ctx)


def fpToSBV_RTZ(v, sort, ctx=None):
    return smts.fpFPToFP(smts.RTZ(), v, sort, ctx)


def fpSignedToFP_RNE(v, sort, ctx=None):
    return smts.fpSignedToFP(smts.RNE(), v, sort, ctx)


def fpUnsignedToFP_RNE(v, sort, ctx=None):
    # The fpToFPUnsigned is anthor option.
    return smts.fpUnsignedToFP(smts.RNE(), v, sort, ctx)
