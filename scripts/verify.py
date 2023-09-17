import parse as ps
import structure as st

import z3

import util as ut


NO_RETURN = {"store"}

float_tolerance = float(0.0001)


def init_solver() -> z3.Solver:
    solver = z3.Solver()
    if st.SOLVER_TIMEOUT > 0:
        solver.set("timeout", st.SOLVER_TIMEOUT * 1000)
    if st.SOLVER_MAX_MEMORY > 0:
        solver.set("max_memory", st.SOLVER_MAX_MEMORY)
    return solver


def smt_add_constraint(
    value: str,
    value_type: str,
    smt: st.VerificationContext(),
    name: str,
    solver: z3.Solver,
):
    # vector type
    assert_waitint_value = smt.get_value_by_name(name)
    if assert_waitint_value is None:
        raise ValueError("Wow we get the empty value here!")
    if ut.is_vec_type(value_type):
        assert_value_input = ps.get_smt_val_vector(value, value_type)
        if not len(assert_value_input) == len(assert_waitint_value):
            raise RuntimeError(
                "The input({}) vector is not same length as the one in smt!".format(
                    value
                )
            )
        for i in range(len(assert_value_input)):
            solver.add(assert_value_input[i] == assert_waitint_value[i])
        return

    ## normal value
    if ps.get_inner_type(value_type) == st.DataType.IntegerType:
        solver.add(assert_waitint_value == int(value))
    elif ps.get_inner_type(value_type) == st.DataType.BooleanType:
        pass  # TODO: raise error or not?
    elif ps.get_inner_type(value_type) == st.DataType.FloatingType:
        solver.add(assert_waitint_value == float(value))
    else:
        raise RuntimeError("Over type({})!".format(value_type))


# TODO: add 0xffff type..
def verify(
    verify_info: st.VerificationLoadInfo,
    load_info: st.LoadAssertInfo,
    verify_mode: bool = True,
):
    solver = init_solver()
    instrs = verify_info.instrs
    smt = st.VerificationContext()
    for loc in range(len(instrs)):
        instr_type = verify_info.get_instr_type(loc)
        value_name = st.get_instr_value_name(instrs[loc], instr_type)

        if value_name == "NoValueName":
            pass
        ps.parse_instr(instrs[loc], instr_type, smt, verify_info.get_instr_dict(loc))
        value_type = smt.get_value_type_by_name(value_name)
        assert_value_str = load_info.get_value_str(loc)
        if ut.is_assert_instr_type(
            instr_type
        ):  # TODO: For the call function not implemented, this is meanningless
            if verify_mode:
                try:
                    smt_add_constraint(
                        assert_value_str, value_type, smt, value_name, solver
                    )
                except ValueError:
                    print("Here happend empty value in {}".format(value_type))
            if solver.check() != z3.sat:
                smt.dump()
                raise RuntimeError(
                    "A value({}) that does not meet expectations was found".format(
                        assert_value_str
                    )
                )

        # replace the val with a value.
        if not ut.no_assertion_value(instr_type) or ps.is_supported_resty(value_type):
            vec_flag = ut.is_vec_type(value_type)
            new_value = ps.get_nn_basedOn_type(value_type, assert_value_str, vec_flag)
            smt.repalce_new_value(value_name, new_value)
    # smt.dump()


def generate_calculate_result(
    verify_info: st.VerificationLoadInfo, load_info: st.LoadAssertInfo
):
    instrs = verify_info.instrs
    smt = st.VerificationContext()
    for loc in range(len(instrs)):
        instr_type = verify_info.get_instr_type(loc)
        value_name = st.get_instr_value_name(instrs[loc], instr_type)
        if value_name == "NoValueName":
            pass
        ps.parse_instr(instrs[loc], instr_type, smt, verify_info.get_instr_dict(loc))
        value_type = smt.get_value_type_by_name(value_name)
        if not ut.no_assertion_value(instr_type) or ps.is_supported_resty(value_type):
            assert_value_str = load_info.get_value_str(loc)
            vec_flag = ut.is_vec_type(value_type)
            new_value = ps.get_nn_basedOn_type(value_type, assert_value_str, vec_flag)
            smt.repalce_new_value(value_name, new_value)
    return smt
    # smt.dump_with_value_name()