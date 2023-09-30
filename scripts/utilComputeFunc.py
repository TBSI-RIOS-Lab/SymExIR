import decimal as dc
from typing import List

import regex as re
import z3


def is_number(string):
    pattern = re.compile(r"^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$")
    return bool(pattern.match(string))


def is_normalizedFloatingPoint(inputStr: str):
    pattern = r"(?P<mantissa>\d+\.\d+)\*\(2\*\*(?P<exponent>\d+)\)"
    match = re.match(pattern, inputStr)
    return True if match is None else False


def normalizedFloatingPoint_to_Decimal(inputStr: str):
    dc.getcontext().prec = 1024
    flag_symbol = True
    if inputStr.startswith("-"):
        flag_symbol = False
        inputStr = inputStr[1:]
    if "*" not in inputStr and is_number(inputStr):
        return dc.Decimal(inputStr)
    pattern = r"(?P<mantissa>\d+"
    if "." in inputStr:
        pattern += r"\.\d+)"
    else:
        pattern += r")"

    if "-" in inputStr:
        pattern += r"\*\(2\*\*(?P<exponent>-\d+)\)"
    else:
        pattern += r"\*\(2\*\*(?P<exponent>\d+)\)"
    match = re.match(pattern, inputStr)
    if not match:
        raise ValueError(f"The inputStr({inputStr}) is not normalizedFloatingPoint!")
    else:
        mantissa = match["mantissa"]
        exponent = match["exponent"]

        res = (
            dc.Decimal(mantissa) * (dc.Decimal(2) ** dc.Decimal(exponent))
            if exponent is not None
            else dc.Decimal(mantissa)
        )
        return res if flag_symbol else -1 * res


def get_compute_result_single(input_number, func):
    if not isinstance(input_number, z3.FPRef):
        raise RuntimeError(f"The input({input_number}) is not z3.FPVal")
    number_decimal = normalizedFloatingPoint_to_Decimal(str(input_number))
    res_decimal = func(number_decimal)
    return z3.FPVal(str(res_decimal), input_number.sort())


def get_compute_result(val, func):
    if isinstance(val, List):
        return [func(val[i]) for i in range(len(val))]
    else:
        return func(val)


def pi():
    """Compute Pi to the current precision.

    >>> print(pi())
    3.141592653589793238462643383

    """
    dc.getcontext().prec += 2  # extra digits for intermediate steps
    three = dc.Decimal(3)  # substitute "three=3.0" for regular floats
    lasts, t, s, n, na, d, da = 0, three, 3, 1, 0, 0, 24
    while s != lasts:
        lasts = s
        n, na = n + na, na + 8
        d, da = d + da, da + 32
        t = (t * n) / d
        s += t
    dc.getcontext().prec -= 2
    return +s


def cos(x):
    """Return the cosine of x as measured in radians.

    The Taylor series approximation works best for a small value of x.
    For larger values, first compute x = x % (2 * pi).

    >>> print(cos(Decimal('0.5')))
    0.8775825618903727161162815826
    >>> print(cos(0.5))
    0.87758256189
    >>> print(cos(0.5+0j))
    (0.87758256189+0j)

    """
    dc.getcontext().prec += 2
    i, lasts, s, fact, num, sign = 0, 0, 1, 1, 1, 1
    while s != lasts:
        lasts = s
        i += 2
        fact *= i * (i - 1)
        num *= x * x
        sign *= -1
        s += num / fact * sign
    dc.getcontext().prec -= 2
    return +s


def sin(x):
    """Return the sine of x as measured in radians.

    The Taylor series approximation works best for a small value of x.
    For larger values, first compute x = x % (2 * pi).

    >>> print(sin(Decimal('0.5')))
    0.4794255386042030002732879352
    >>> print(sin(0.5))
    0.479425538604
    >>> print(sin(0.5+0j))
    (0.479425538604+0j)

    """
    dc.getcontext().prec += 2
    i, lasts, s, fact, num, sign = 1, 0, x, 1, x, 1
    while s != lasts:
        lasts = s
        i += 2
        fact *= i * (i - 1)
        num *= x * x
        sign *= -1
        s += num / fact * sign
    dc.getcontext().prec -= 2
    return +s


def get_sin_result(val):
    return get_compute_result(val, get_sin_result_single)


def get_sin_result_single(input_number):
    return get_compute_result_single(input_number, sin)


def get_cos_result(val):
    return get_compute_result(val, get_cos_result_single)


def get_cos_result_single(input_number):
    return get_compute_result_single(input_number, cos)


def get_exp_result(val):
    return get_compute_result(val, get_exp_result_single)


def get_exp_result_single(input_number):
    return get_compute_result_single(input_number, exp)


def get_exp2_result(val):
    return get_compute_result(val, get_exp2_result_single)


def get_exp2_result_single(input_number):
    return get_compute_result_single(input_number, exp2)


def get_log_result(val):
    return get_log10_result(val)


def get_log10_result(val):
    return get_compute_result(val, get_log10_result_single)


def get_log10_result_single(input_number):
    return get_compute_result_single(input_number, log10)


def get_log2_result(val):
    return get_compute_result(val, get_log2_result_single)


def get_log2_result_single(input_number):
    return get_compute_result_single(input_number, log2)


def get_ldexp_result_single(float_n, int_n):
    if not isinstance(float_n, z3.FPRef):
        raise RuntimeError("The input({}) is not z3.FPVal".format(float_n))

    f_input = str(float_n)
    i_input = dc.Decimal(str(int_n))
    number_decimal = normalizedFloatingPoint_to_Decimal(f_input)
    res_decimal = ldexp(i_input, number_decimal)
    return z3.FPVal(str(res_decimal), float_n.sort())


def get_floor_result(val):
    return get_compute_result(val, get_floor_result_single)


def get_floor_result_single(input_number):
    return get_compute_result_single(input_number, floor)


def get_ceil_result(val):
    return get_compute_result(val, get_ceil_result_single)


def get_ceil_result_single(input_number):
    return get_compute_result_single(input_number, ceil)


def get_nearbyint_result(val):
    return get_round_result(val)


def get_round_result(val):
    return get_compute_result(val, get_round_result_single)


def get_round_result_single(input_number):
    return get_compute_result_single(input_number, round)


def get_trunc_result(val):
    return get_compute_result(val, get_trunc_result_single)


def get_trunc_result_single(input_number):
    return get_compute_result_single(input_number, trunc)


def ldexp(int_number, float_number):
    res = 0
    if isinstance(float_number, dc.Decimal) and isinstance(int_number, dc.Decimal):
        dc.getcontext().prec += 2
        res = int_number * float_number.exp()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def exp(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.exp()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def exp2(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = dc.Decimal(2) ** x
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def log(x):
    return log10(x)


def floor(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.__floor__()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def ceil(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.__ceil__()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def trunc(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.__trunc__()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def nearbyint(x):
    return round(x)


def round(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = round(x)
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def log10(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.log10()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")


def log2(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.log10() / dc.Decimal(2).log10()
        dc.getcontext().prec -= 2
        return res
    else:
        raise RuntimeError("The input type is not Decimal!\n")
