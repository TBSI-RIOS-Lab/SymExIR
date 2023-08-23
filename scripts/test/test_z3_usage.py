import decimal as dc
import z3

def test_list_z3():
    l: list = []
    l.append(z3.Int("x"))
    l.append(z3.Int("y"))
    l.append(z3.Int("z"))
    solver = z3.Solver()
    solver.add(l[2] - l[1] == 0)
    solver.add(l[2] == 3)
    solver.add(l[1] + l[0] == l[2])
    solver.add(l[0] >= 0)
    solver.add(l[0] >= 0)
    assert solver.check() == z3.sat
    print(solver.model())


def test_list_z3_1():
    l: list = []
    l.append(z3.Int("x"))
    l.append(z3.Int("y"))
    l.append(l[0] + l[1])
    solver = z3.Solver()
    solver.add(l[2] == 1)
    assert solver.check() == z3.sat
    print(solver.model())
    print(type(l[2]))
    print(type(l[0]))


def test_z3_reset():
    l: list = []
    l.append(z3.BitVecVal(10, 32))
    l.append(z3.BitVecVal(10, 32))
    l.append(l[0] + l[1])
    solver = z3.Solver()
    solver.add(l[2] == 20)
    assert solver.check() == z3.sat
    print(solver.model())


def test_z3_val():
    a = z3.BitVecVal(10, 32)
    print("0x%.8x" % a.as_long())
    print("0x%.8x" % a.as_signed_long())


def test_z3_add():
    l: list = []
    l.append(z3.BitVecVal(10, 32))
    l.append(z3.BitVecVal(10, 32))
    l.append(l[0] + l[1])
    solver = z3.Solver()
    solver.add(l[2] == 20)
    assert solver.check() == z3.sat
    print(solver.model())
    solver.add(l[2] == z3.BitVecVal(20, 32))
    assert solver.check() == z3.sat
    print(solver.model())


def test_float_val_z3_solver():
    dc.getcontext().prec = 128
    solver = z3.Solver()
    a = "1e2"
    b = float(a)
    c = dc.Decimal(a)
    x = z3.FPVal(20.0, z3.FPSort(8, 24))
    y = z3.FPVal(20.000000000001, z3.FPSort(8, 24))
    c = z3.fpAdd(z3.RTZ(), x, y)
    z = z3.FPVal("12020000.10002", z3.FPSort(8, 24))
    print(z)
    solver.add(c == 40.00000000000)
    e = dc.Decimal("12323e222323")
    
    z = z3.FPVal("1.5258796215057373046875*(2**17)", z3.FPSort(8, 24))
    print()
    print(z)
    assert solver.check() == z3.sat


if __name__ == "__main__":
    # test_list_z3()
    # test_list_z3_1()
    # test_z3_reset()
    # test_z3_val()
    # test_z3_add()
    test_float_val_z3_solver()
