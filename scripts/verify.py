from structure import *


def init_solver():
    solver = z3.Solver()
    if SOLVER_TIMEOUT > 0:
        solver.set("timeout", SOLVER_TIMEOUT * 1000)
    if SOLVER_MAX_MEMORY > 0:
        solver.set("max_memory", SOLVER_MAX_MEMORY)
    return solver


def verify(smts: list[z3.ExprRef], verify_info):
    solver = init_solver()
