import decimal as dc
import regex as re

def normalizedFloatingPointtoDecimal(inputStr: str):
    dc.getcontext().prec = 1024
    pattern = r"(?P<mantissa>\d+\.\d+)\*\(2\*\*(?P<exponent>\d+)\)"
    match = re.match(pattern, inputStr)
    if not match:
        raise ValueError("The inputStr({}) is not normalizedFloatingPoint!")
    else: 
        mantissa = match["mantissa"]
        exponent = match["exponent"]
        print(exponent)
        return dc.Decimal(mantissa)*(dc.Decimal(2)**dc.Decimal(exponent))

def pi():
    """Compute Pi to the current precision.

    >>> print(pi())
    3.141592653589793238462643383

    """
    dc.getcontext().prec += 2  # extra digits for intermediate steps
    three = dc.Decimal(3)      # substitute "three=3.0" for regular floats
    lasts, t, s, n, na, d, da = 0, three, 3, 1, 0, 0, 24
    while s != lasts:
        lasts = s
        n, na = n+na, na+8
        d, da = d+da, da+32
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
        fact *= i * (i-1)
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
        fact *= i * (i-1)
        num *= x * x
        sign *= -1
        s += num / fact * sign
    dc.getcontext().prec -= 2
    return +s

def exp(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.exp()
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


def log(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.logb()
        dc.getcontext().prec -= 2
        return res
    else: 
        raise RuntimeError("The input type is not Decimal!\n")


def log2(x):
    res = 0
    if isinstance(x, dc.Decimal):
        dc.getcontext().prec += 2
        res = x.logb()
        dc.getcontext().prec -= 2
        return res
    else: 
        raise RuntimeError("The input type is not Decimal!\n")