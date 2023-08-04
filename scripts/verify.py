from scripts.util import is_assert_instr_type, is_constraint_type
from structure import *
import parse as ps

NO_RETURN = {"store"}

float_tolerance = float(0.0001)


def init_solver() -> z3.Solver:
    solver = z3.Solver()
    if SOLVER_TIMEOUT > 0:
        solver.set("timeout", SOLVER_TIMEOUT * 1000)
    if SOLVER_MAX_MEMORY > 0:
        solver.set("max_memory", SOLVER_MAX_MEMORY)
    return solver


def smt_add_constraint(value: str, value_type: str, assert_value, solver: z3.Solver):
    if value_type == "int":
        solver.add(assert_value == int(value))
    elif value_type == "float":
        solver.add(
            assert_value - float(value) > 0
            and assert_value - float(value) < float_tolerance
        )


def verify(
    smts: list[z3.ExprRef], verify_info: VerificationLaodInfo, load_info: LoadAssertInfo
):
    solver = init_solver()
    instrs = verify_info.instrs
    smt = VerificationContext()
    for loc in range(len(instrs)):
        instr_type = verify_info.get_instr_type(loc)
        value_name = get_instr_value_name(instrs[loc])
        
        if value_name == "NoValueName":
            pass

        ps.parse_instr(instrs[loc], instr_type, smt, verify_info.get_instr_dict(loc))
        value_type = smt.get_value_type_by_name(value_name)
        assert_value_str = load_info.get_value(loc)
        if is_assert_instr_type(instr_type):
            solver.reset()

            # add assertion
            smt_add_constraint(assert_value_str, value_type, smt.find_value_by_name(value_name), solver) 
            if solver.check() != z3.sat:
                raise RuntimeError("A value that does not meet expectations was found")
            
        # replace the val with a value.
        vec_flag = ps.is_vec_type(value_type)
        new_value = ps.get_nn_basedOn_type(value_type, assert_value_str, vec_flag)
        smt.repalce_new_value(value_name, new_value)
