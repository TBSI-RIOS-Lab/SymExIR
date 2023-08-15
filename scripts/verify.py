import parse as ps
from structure import *

from util import is_assert_instr_type, is_constraint_type, is_read_from_memory_instr_type

NO_RETURN = {"store"}

float_tolerance = float(0.0001)


def init_solver() -> z3.Solver:
    solver = z3.Solver()
    if SOLVER_TIMEOUT > 0:
        solver.set("timeout", SOLVER_TIMEOUT * 1000)
    if SOLVER_MAX_MEMORY > 0:
        solver.set("max_memory", SOLVER_MAX_MEMORY)
    return solver


def smt_add_constraint(
    value: str,
    value_type: str,
    smt: VerificationContext(),
    name: str,
    solver: z3.Solver,
):
    if ps.get_inner_type(value_type) == DataType.IntegerType:
        solver.add(smt.get_value_by_name(name) == int(value))
    elif ps.get_inner_type(value_type) == DataType.BooleanType:
        pass  # TODO: raise error or not?
    elif ps.get_inner_type(value_type) == DataType.FloatingType:
        solver.add(
            smt.get_value_by_name(name) - float(value) > 0
            and smt.get_value_by_name(name) - float(value) < float_tolerance
        )
    else:
        raise RuntimeError("Over type({})!".format(value_type))


def verify(verify_info: VerificationLaodInfo, load_info: LoadAssertInfo, verify_mode: bool = True):
    solver = init_solver()
    instrs = verify_info.instrs
    smt = VerificationContext()
    for loc in range(len(instrs)):
        instr_type = verify_info.get_instr_type(loc)
        value_name = get_instr_value_name(instrs[loc], instr_type)

        if value_name == "NoValueName":
            pass

        ps.parse_instr(instrs[loc], instr_type, smt, verify_info.get_instr_dict(loc))
        value_type = smt.get_value_type_by_name(value_name)
        assert_value_str = load_info.get_value_str(loc)
        if is_assert_instr_type(instr_type):
            # add assertion
            if verify_mode:
                smt_add_constraint(assert_value_str, value_type, smt, value_name, solver)
            if solver.check() != z3.sat:
                raise RuntimeError("A value that does not meet expectations was found")

        # replace the val with a value.
        vec_flag = ps.is_vec_type(value_type)
        new_value = ps.get_nn_basedOn_type(value_type, assert_value_str, vec_flag)
        smt.repalce_new_value(value_name, new_value)
    # smt.dump()


def generate_calculate_result(verify_info: VerificationLaodInfo, load_info: LoadAssertInfo):
    instrs = verify_info.instrs
    smt = VerificationContext()
    for loc in range(len(instrs)):
        instr_type = verify_info.get_instr_type(loc)
        value_name = get_instr_value_name(instrs[loc], instr_type)
        if value_name == "NoValueName":
            pass
        ps.parse_instr(instrs[loc], instr_type, smt, verify_info.get_instr_dict(loc))
        value_type = smt.get_value_type_by_name(value_name)
        if is_read_from_memory_instr_type(instr_type):
            assert_value_str = load_info.get_value_str(loc)
            vec_flag = ps.is_vec_type(value_type)
            new_value = ps.get_nn_basedOn_type(value_type, assert_value_str, vec_flag)
            smt.repalce_new_value(value_name, new_value)
    return smt
    # smt.dump_with_value_name()