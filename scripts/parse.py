import operator as opt
from copy import deepcopy
from typing import Dict, List, Set, Tuple

import llvmlite.binding as llvm
import regex as re
import structure as st
import z3
import z3Extension as z3e

CARE_OPCODE = {
    "ret",
    "br",
    "switch",
    "indirectbr",
    "invoke",
    "callbr",
    "resume",
    "catchswitch",
    "catchret",
    "cleanupret",
    "unreachable",
    "fneg",
    "add",
    "fadd",
    "sub",
    "fsub",
    "mul",
    "fmul",
    "udiv",
    "sdiv",
    "fdiv",
    "urem",
    "srem",
    "frem",
    "shl",
    "lshr",
    "ashr",
    "and",
    "or",
    "xor",
    "extractelement",
    "insertelement",
    "shufflevector",
    "insertvalue",
    "extractvalue",
    "alloca",
    "load",
    "store",
    "fence",
    "cmpxchg",
    "atomicrmw",
    "getelementptr",
    "trunc",
    "zext",
    "sext",
    "fptrunc",
    "fpext",
    "fptoui",
    "fptosi",
    "uitofp",
    "sitofp",
    "ptrtoint",
    "inttoptr",
    "bitcast",
    "addrspacecast",
    "icmp",
    "fcmp",
    "phi",
    "select",
    "freeze",
    "call",
    "va_arg",
    "landingpad",
    "catchpad",
    "cleanuppad",
}

NO_RETURN = {"store"}

terminator_instr_group = {
    "ret",
    "br",
    "switch",
    "indirectbr",
    "invoke",
    "callbr",
    "resume",
    "catchswitch",
    "catchret",
    "cleanupret",
    "unreachable",
}

regular_group: Set = {"add", "sub", "mul", "shl"}
flaot_group: Set = {"fdiv", "fmul", "fsub", "fadd", "frem"}
extact_flag_group: Set = {"udiv", "sdiv", "lshr", "ashr"}
type_twoop_orv_group: Set = {"urem", "srem", "and", "or", "xor"}
unary_flaot_operators = {"fneg"}
extractelement_type = {"extractelement"}
insertelement_type = {"insertelement"}
shufflevector_type = {"shufflevector"}
conversion_operations_group = {
    "trunc",
    "zext",
    "sext",
    "fptrunc",
    "fpext",
    "fptoui",
    "fptosi",
    "uitofp",
    "sitofp",
    "inttoptr",  # TODO: The "inttoptr" and "addrspacecast" need check!
    "bitcast",
    "ptrtoint",
}

""""
    Only support the most basic edtion just like:
    <result> = extractvalue {i32, float} %agg, 0
    %agg1 = insertvalue {i32, float} undef, i32 1, 0
"""
extractvalue_group = {"extractvalue"}
insertvalue_group = {"insertvalue"}
icmp_group = {"icmp"}
fcmp_group = {"fcmp"}
select_type = {"select"}
over_bb_type = {
    "freeze",
    "phi",
    "va_arg",
    "landingpad",
    "catchpad",
    "cleanuppad",
}  # TODO: add description of getelementptr in document

simple_atomic_group = {"fence"}
memory_group = {"cmpxchg", "atomicrmw", "addrspacecast"}
store_type = {
    "store"
}  # Actually for now the "store" is meaningless for the whole program, but we still finish that.
alloca_type = {"alloca"}
load_type = {"load"}
call_type = {"call"}
getelementptr_type = {"getelementptr"}
llvm_instr = {"llvm.minnum"}


ptr_instr = {"ptrtoint", "bitcast", "inttoptr"}

regex_fast_math_flag = "(nnan |ninf |nsz |arcp |contract |afn |reassoc |fast )"
regex_type_two_op_orv = (
    "(?P<type><.*x.*>|.*?) (?P<firstop><.*,.*>|.*?), (?P<secondop><.*,.*>|.*?)"
)
regex_nuw_nsw = "(nuw |nsw )"
regex_exact = "(exact )"
regex_type_secondop_nov = "(?P<ty1>.*?) (?P<op1>.*?)"
regex_vscale_n_t = "<((?P<vs>.*?) x ){0,1}(?P<n>.*?) x (?P<ty>.*?)> (?P<val>.*?)"
regex_vscale_n_ty = "<((?P<vs>.*?) x ){0,1}(?P<n>.*?) x (?P<ty>.*?)>"
regex_tmp = ".*"
regex_cconv_flag = "(fastcc |ccc |coldcc |cc 10 |cc 11 |webkit_jscc |anyregcc |preserve_mostcc |cxx_fast_tlscc |tailcc |swiftcc |swifttailcc |cfguard_checkcc |cc <.*>)"
# NOTE: The poison value is ignored.

vec_ty_example = "<1 x i32>"


class SliceToken:
    def __init__(
        self,
        type: str,
        return_value_name: str,
        return_value_type: str,
        opcode: str,
        slice: str,
    ) -> None:
        self._type: str = type
        self._slices: str = slice
        self._return_value_name: str = return_value_name
        self._return_value_type: str = return_value_type
        self._opcode = opcode

    @property
    def type(self) -> str:
        return self._type

    @property
    def return_value_name(self) -> str:
        return self._return_value_name

    @property
    def return_value_type(self) -> str:
        return self._return_value_type

    @property
    def slice(self) -> str:
        return self._slices


def is_number(string):
    pattern = re.compile(r"^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$")
    return bool(pattern.match(string))


def get_opcode(s: str):
    """This function is not recommended since it lacks a
    check to ensure that the input obeys the LLVM instruction command."""
    if "," in s:
        raise ValueError("There is ',' in input!\n")
    for part in s.split(" "):
        ps = part.strip()
        if ps in CARE_OPCODE:
            return ps
    return "unimplemented"


def have_return(s: str) -> bool:
    if "=" in s:
        return True
    else:
        return False


def slice_instr(s: str, type: str, opcode: str) -> SliceToken:
    s = s.strip().split(";")[0].strip()
    if have_return(s):
        ps = s.split("=")
        re_value_name = ps[0].strip()
        re_value_type = type
        token = SliceToken(
            "NOVOID", re_value_name, re_value_type, opcode, ps[1].strip()
        )
        return token
    else:
        token = SliceToken("VOID", "", "VOID", opcode, s.strip())
        return token


def parse_ll(ll_moudle: llvm.ModuleRef):
    for function in ll_moudle.functions:
        pass  # TODO: unfinished part which need check the plan once more!
    pass


def extra_slice_token(token_ex: str, instr_type: str) -> re.Match[str] | None:
    pattern = None
    if instr_type in terminator_instr_group:
        pattern = re.compile("")  # Return empty dict.
    elif instr_type in regular_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + regex_nuw_nsw
            + "{0,2}"
            + regex_type_two_op_orv
            + "$"
        )

    elif instr_type in flaot_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + regex_fast_math_flag
            + "{0,8}"
            + regex_type_two_op_orv
            + "$"
        )

    elif instr_type in extact_flag_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + regex_exact  # TODO: The keyword exact is not in our consideration.
            + "{0,1}"
            + regex_type_two_op_orv
            + "$"
        )

    elif instr_type in type_twoop_orv_group:
        pattern = re.compile("^" + instr_type + " " + regex_type_two_op_orv + "$")

    elif instr_type in unary_flaot_operators:
        pattern = re.compile(
            "^" + instr_type + " " + "(?P<type><.*x.*>|.*?) (?P<op1>.*?)$"
        )

    elif instr_type in extractelement_type:
        pattern = re.compile(
            "^extractelement " + regex_vscale_n_t + ", " + regex_type_secondop_nov + "$"
        )

    elif instr_type in insertelement_type:
        pattern = re.compile(
            "^insertelement "
            + regex_vscale_n_t
            + ", (?P<ty1>.*?) (?P<elt>.*?), (?P<ty2>.*?) (?P<idx>.*?)"
            + "$"
        )
    elif instr_type in shufflevector_type:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "<((?P<v1_vs>.*?) x ){0,1}(?P<v1_n>.*?) x (?P<v1_ty>.*?)>"
            + " (?P<v1>.*?), "
            + "<((?P<v2_vs>.*?) x ){0,1}(?P<v2_n>.*?) x (?P<v2_ty>.*?)>"
            + " (?P<v2>.*?), "
            + "<((?P<mask_vs>.*?) x ){0,1}(?P<mask_n>.*?) x (.*?)>"
            + " (?P<v3>.*?)$"
        )
    elif instr_type in conversion_operations_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(?P<ty1><.*x.*>|.*?) (?P<val>.*?)"
            + " to "
            + "(?P<ty2><.*x.*>|.*?)$"
        )

    elif instr_type in extractvalue_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(?P<type>\{.*?\}) "
            + "(?P<op_val>.*?), "
            + "(?P<idx>.*?)"
            + "$"
        )

    elif instr_type in insertvalue_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(?P<type>\{.*?\}) "
            + "(?P<op_val>.*?), "
            + "(?P<idx>.*?)"
            + "$"
        )

    elif instr_type in getelementptr_type:
        pattern = re.compile("")

    elif instr_type in icmp_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(?P<cond>.*?) (?P<ty><.*x.*>|.*?) (?P<op1><.*>|.*?), (?P<op2><.*>|.*?)$"
        )

    elif instr_type in fcmp_group:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + regex_fast_math_flag
            + "{0,8}"
            + "(?P<cond>.*?) (?P<ty><.*x.*>|.*?) (?P<op1><.*>|.*?), (?P<op2><.*>|.*?)$"
        )

    elif instr_type in select_type:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + regex_fast_math_flag
            + "{0,8}"
            + "(?P<selty><.*x.*>|.*?) "
            + "(?P<cond>.*?), (?P<ty><.*x.*>|.*?) (?P<op1><.*>|.*?), (?P<ty><.*x.*>|.*?) (?P<op2><.*>|.*?)$"
        )

    elif instr_type in simple_atomic_group:
        pattern = re.compile("")

    elif instr_type in memory_group:
        pattern = re.compile("")

    elif instr_type in store_type:
        # The type of the <pointer> operand must be a pointer to the first class type of the <value> operand
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(atomic ){0,1}"
            + "(volatile ){0,1}"
            + "(?P<ty><.*x.*>|.*?) "
            + "(?P<value><.*x.*>|.*?), (?P<ptr_ty><.*x.*>\*|.*?) "
            + "(?P<pointer>.*?)"
            + "(,.*?){0,1}$"
        )

    elif instr_type in alloca_type:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(inalloca ){0,1}"
            + "(?P<ty><.*x.*>|.*?)"
            + "(,.*?){0,1}"
            + "(align (?P<align>.*)){0,1}$"
        )

    elif instr_type in load_type:
        "example: 'ty: i32'"
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(atomic ){0,1}"
            + "(volatile ){0,1}"
            + "(?P<ty><.*>|.*?)"
            + ",.*$"
        )
    elif instr_type in call_type:
        "exampl:  call i8 @llvm.smax.i8(i8 42, i8 -24)"
        "The non llvm function is not in our consideration."
        if opt.contains(token_ex, "llvm"):
            pattern = re.compile(
                "^"
                + "(tail | musttail | notail ){0,1}"
                + "call"
                + regex_fast_math_flag
                + "{0,8}"
                + regex_cconv_flag
                + "{0,1}"
                + "(zeroext |signext |inreg )"
                + "{0,1}"
                + " (?P<ty><.*>|.*?) "
                + "(?P<function>@.*)"
                + ".*$"
            )
        else:
            pattern = re.compile("")

    if pattern != None:
        gs = re.search(
            pattern,
            token_ex,
        )
        return gs


Name2Type = {
    "ptr": st.DataType.IntegerType,  # The format of the pointer is specified as i64 by default.
    "i1": st.DataType.IntegerType,
    "i8": st.DataType.IntegerType,
    "i16": st.DataType.IntegerType,
    "i32": st.DataType.IntegerType,
    "i64": st.DataType.IntegerType,
    "bfloat": st.DataType.FloatingType,
    "half": st.DataType.FloatingType,
    "float": st.DataType.FloatingType,
    "double": st.DataType.FloatingType,
    "quad": st.DataType.FloatingType,
    "x86_fp80": st.DataType.FloatingType,
    "v64": st.DataType.VectorType,
    "v128": st.DataType.VectorType,
}


TypeAlias = {"f32:32:32": "float", "f64:64:64": "double", "f128:128:128": "quad"}


TypePrecision = {
    "ptr": 64,
    "i1": 1,
    "i8": 8,
    "i16": 16,
    "i32": 32,
    "i64": 64,
    "bfloat": 16,
    "half": 16,
    "float": 32,
    "double": 64,
    "quad": 128,
    "x86_fp80": 80,
    "v64": 64,
    "v128": 128
    # "a" : 8,
}

SimpleType = {
    "i1",
    "i8",
    "i16",
    "i32",
    "i64",
    "bfloat",
    "half",
    "float",
    "double",
    "quad",
    "x86_fp80",
    "v64",
    "v128",
}


def change_ptr_format(precision: int):
    TypePrecision["ptr"] = precision


def get_inner_type(instr_type: str) -> st.DataType:
    if instr_type not in Name2Type.keys():
        raise NotImplementedError("The type({}) is not implemented!".format(instr_type))
    return Name2Type[instr_type]


def get_type_precision(instr_type: str) -> int:
    if instr_type not in Name2Type.keys():
        raise NotImplementedError(
            "The type({}) is not TypePrecision!".format(instr_type)
        )
    return TypePrecision[instr_type]


def get_basic_smt_sort(var_type: str) -> z3.SortRef:
    """Return the SMT sort for the llvm sort."""
    if get_inner_type(var_type) == st.DataType.IntegerType:
        return z3.BitVecSort(get_type_precision(var_type))
    if get_inner_type(var_type) == st.DataType.BooleanType:
        return z3.BoolSort()
    if get_inner_type(var_type) == st.DataType.FloatingType:
        precision = get_type_precision(var_type)
        if precision == 16:
            return z3.Float16()
        if precision == 32:
            return z3.Float32()
        if precision == 64:
            return z3.Float64()
        if precision == 80:
            # 80-bit floats does not follow the IEEE standard, so this is
            # only for x86_fp80
            return z3.FPSort(15, 64)
        if precision == 128:
            return z3.Float128()

    raise NotImplementedError(f"get_smt_sort {var_type.__class__}")


def get_basic_smt_value(name: str, type: str):
    """Return the SMT sort for the llvm sort."""
    smt_sort = get_basic_smt_sort(type)
    if get_inner_type(type) == st.DataType.IntegerType:
        return z3.BitVec(name, smt_sort)
    if get_inner_type(type) == st.DataType.BooleanType:
        return z3.Bool(name)
    if get_inner_type(type) == st.DataType.FloatingType:
        return z3.FP(name, smt_sort)

    raise NotImplementedError(f"get_smt_sort {type.__class__}")


def get_basic_smt_val(
    var_type: str, value: float | int
) -> z3.BitVecNumRef | z3.BoolRef | z3.FPNumRef:
    smt_sort = get_basic_smt_sort(var_type)
    if get_inner_type(var_type) == st.DataType.IntegerType:
        return z3.BitVecVal(value, smt_sort)
    elif get_inner_type(var_type) == st.DataType.BooleanType:
        return z3.BoolVal(value)
    elif get_inner_type(var_type) == st.DataType.FloatingType:
        return z3.FPVal(value, smt_sort)
    else:
        raise RuntimeError("There is value not that simple.\n")


def is_simple_type(var_type) -> bool:
    if var_type in SimpleType:
        return True
    return False


def parse_instr_load(value_name: str, data_token: Dict, smt_block: st.VerificationInfo):
    if data_token == None or "ty" not in data_token.keys():
        raise RuntimeError("Wrong data_token({}) tranfer!".format(data_token))

    if not smt_block.is_there_same_value(value_name):
        ty = data_token["ty"]
        if is_simple_type(ty):
            value = get_basic_smt_value(value_name, ty)
            smt_block.add_new_value(value_name, value, ty)
        elif is_vec_type(ty):
            value = get_smt_vector(value_name, ty)
            smt_block.add_new_value(value_name, value, ty)


def parse_instr_getelementptr(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    if data_token != None and len(data_token):
        raise RuntimeError("The data_token for getelementptr should be empty.\n")

    value = get_basic_smt_value(value_name, "ptr")
    smt_block.add_new_value(value_name, value, "ptr")


def is_vec_type(value_type: str):
    if value_type.startswith("<"):
        return True
    else:
        return False


def get_info_from_vector_type(value_type: str) -> Tuple[int, str]:
    pattern = re.compile("<(?P<size>.*?) x (?P<type>.*?)>")
    search_result = re.search(pattern, value_type.strip(" "))
    if search_result != None:
        return int(search_result["size"]), search_result["type"]
    else:
        raise ValueError("The input vector type is wrong!\n")


def get_smt_vector(value_name, vec_type):
    """
    >>> value_name = "%1"
    >>> vec_type = "<2 x i32>"
    >>> X = get_smt_vector(value_name, vec_type)
    >>> X
    [%1__0, %1__1]
    """
    size, var_type = get_info_from_vector_type(vec_type)
    sort = get_basic_smt_sort(var_type)
    if get_inner_type(var_type) == st.DataType.IntegerType:
        return z3e.BvVector(value_name, size, sort)
    elif get_inner_type(var_type) == st.DataType.FloatingType:
        return z3e.FpVector(value_name, size, sort)
    else:
        raise NotImplementedError("")


def get_smt_val_vector(value_vec, vec_type):
    """
    >>> value_name = "< i32 1, i32 1>"
    >>> vec_type = "<2 x i32>"
    >>> X = get_smt_val_vector(value_name, vec_type)
    >>> X
    [1, 1]
    >>> value_name = "< float 1.0, float 1.0>"
    >>> vec_type = "<2 x float>"
    >>> X = get_smt_val_vector(value_name, vec_type)
    """
    size, var_type = get_info_from_vector_type(vec_type)
    values = value_vec.strip("<").strip(">").strip(" ").split(",")
    values = [values[i].strip(" ") for i in range(len(values))]
    v_list = []
    for value_vec in values:
        res_split = value_vec.split()
        assert len(res_split) == 2
        key1 = res_split[0]
        key2 = res_split[1]
        if key1 != var_type:
            raise TypeError("The var_type in list is not same as vec_type!\n")
        v_list.append(key2)
    sort = get_basic_smt_sort(var_type)
    if get_inner_type(var_type) == st.DataType.IntegerType:
        return z3e.BitvalVector(v_list, sort)
    elif get_inner_type(var_type) == st.DataType.FloatingType:
        return z3e.FpValVector(v_list, sort)
    else:
        raise NotImplementedError("")


def get_nn_basedOn_type(
    v_type: str, value: str, is_vec: bool
) -> z3.BitVecNumRef | z3.BoolRef | z3.FPNumRef | List:
    "return real val for the input."
    if is_vec and is_vec_type(v_type):
        return get_smt_val_vector(value, v_type)
    else:
        if not is_number(value):
            raise TypeError("The value is not digit")
        value_number = eval(value)
        res = get_basic_smt_val(v_type, value_number)
        return res


def get_value_from_smt(one: str, smt_block: st.VerificationInfo):
    if one.startswith("%"):
        value = smt_block.find_value_by_name(one)
    else:
        raise RuntimeError("The value name is started with %.")
    return value


def get_single_value(one: str, smt_block: st.VerificationInfo, value_type: str):
    value_vec_type = is_vec_type(value_type)
    if one.startswith("%"):
        return get_value_from_smt(one, smt_block)
    else:
        return get_nn_basedOn_type(value_type, one, value_vec_type)


def get_two_value(
    first: str, second: str, smt_block: st.VerificationInfo, value_type: str
):
    a = get_single_value(first, smt_block, value_type)

    b = get_single_value(second, smt_block, value_type)
    return a, b


def get_ready_two_value_basic(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    if smt_block.is_there_same_value(value_name):
        raise ValueError(
            "There is already a same name({}) in smt_block!".format(value_name)
        )
    firstop = data_token["firstop"]
    secondop = data_token["secondop"]
    value_type = data_token["type"]
    # TODO: The date_token[] have no check for the key! Change it.
    return get_two_value(firstop, secondop, smt_block, value_type)


def is_z3_vector(var):
    return isinstance(var, List)


def is_same_z3_vector_type(var1, var2):
    "Check if the two argument are same z3 type in python list"
    # TODO: The check here is too weak.
    if is_z3_vector(var1) and is_z3_vector(var2):
        if len(var1) != len(var2):
            return False
        else:
            return True
    else:
        return False


def parse_instr_two_op_function(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
    z3_function_two_op,
):
    first, second = get_ready_two_value_basic(value_name, data_token, smt_block)
    res = z3.simplify(z3_function_two_op(first, second))
    ty = data_token["type"]
    smt_block.add_new_value(value_name, res, ty)


def parse_instr_add(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecAdd)


def parse_instr_sub(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecSub)


def parse_instr_mul(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecMul)


def parse_instr_shl(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecShl)


def get_icmp_result(first_value, second_value, cond: str):
    assert not isinstance(first_value, List)
    assert not isinstance(second_value, List)
    assert not isinstance(first_value, z3.BoolRef)
    assert not isinstance(second_value, z3.BoolRef)
    res = None
    if cond == "eq":
        res = z3.BoolVal(z3.eq(first_value, second_value))
    elif cond == "ne":
        res = z3.Not(z3.eq(first_value, second_value))
    elif cond == "ugt":
        res = z3.UGT(first_value, second_value)
    elif cond == "uge":
        res = z3.UGE(first_value, second_value)
    elif cond == "ult":
        res = z3.ULT(first_value, second_value)
    elif cond == "ule":
        res = z3.ULE(first_value, second_value)
    elif cond == "sgt":
        res = first_value > second_value
    elif cond == "sge":
        res = first_value >= second_value
    elif cond == "slt":
        res = first_value < second_value
    elif cond == "sle":
        res = first_value <= second_value
    else:
        raise RuntimeError("There is a instr type not included.")
    res = z3e.Bool2BitVector1(res)
    return res


# Have not taken "ptr" into c
def parse_instr_icmp(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    cond, ty, op1, op2 = (
        data_token["cond"],
        data_token["ty"],
        data_token["op1"],
        data_token["op2"],
    )
    first_value = get_single_value(op1, smt_block, ty)
    second_value = get_single_value(op2, smt_block, ty)
    res = get_icmp_result(first_value, second_value, cond)
    smt_block.add_new_value(value_name, res, "i1")


def get_fcmp_result(first_value, second_value, cond: str):
    ordered_group = {"oeq", "ogt", "oge", "olt", "ole", "one", "ord"}
    unordered_group = {"ueq", "ugt", "uge", "ult", "ule", "une", "uno"}
    res = None
    if cond == "false":
        res = z3.BoolVal(False)
    elif cond == "true":
        res = z3.BoolVal(True)
    elif cond in ordered_group:
        res = z3.And(z3.Not(z3.fpIsNaN(first_value)), z3.Not(z3.fpIsNaN(second_value)))
        if cond == "oeq":
            res = z3.And(res, z3.fpEQ(first_value, second_value))
        elif cond == "ogt":
            res = z3.And(res, z3.fpGT(first_value, second_value))
        elif cond == "oge":
            res = z3.And(res, z3.fpGEQ(first_value, second_value))
        elif cond == "olt":
            res = z3.And(res, z3.fpLT(first_value, second_value))
        elif cond == "ole":
            res = z3.And(res, z3.fpLEQ(first_value, second_value))
        elif cond == "one":
            res = z3.And(res, z3.fpNEQ(first_value, second_value))
        elif cond == "ord":
            pass
        else:
            raise RuntimeError("There is one cond({}) over range.".format(cond))
    elif cond in unordered_group:
        res = z3.Or(z3.fpIsNaN(first_value), z3.fpIsNaN(second_value))
        if cond == "ueq":
            res = z3.Or(res, z3.fpEQ(first_value, second_value))
        elif cond == "ugt":
            res = z3.Or(res, z3.fpGT(first_value, second_value))
        elif cond == "uge":
            res = z3.Or(res, z3.fpGEQ(first_value, second_value))
        elif cond == "ult":
            res = z3.Or(res, z3.fpLT(first_value, second_value))
        elif cond == "ule":
            res = z3.Or(res, z3.fpLEQ(first_value, second_value))
        elif cond == "une":
            res = z3.Or(res, z3.fpNEQ(first_value, second_value))
        elif cond == "uno":
            pass
        else:
            raise RuntimeError("There is one cond({}) over range.".format(cond))
    res = z3.simplify(z3e.Bool2BitVector1(res))
    return res


def parse_instr_fcmp(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    ordered_group = {"oeq", "ogt", "oge", "olt", "ole", "one", "ord"}
    unordered_group = {"ueq", "ugt", "uge", "ult", "ule", "une", "uno"}
    cond, ty, op1, op2 = (
        data_token["cond"],
        data_token["ty"],
        data_token["op1"],
        data_token["op2"],
    )
    first_value = get_single_value(op1, smt_block, ty)
    second_value = get_single_value(op2, smt_block, ty)
    res = get_fcmp_result(first_value, second_value, cond)
    smt_block.add_new_value(value_name, res, "i1")


def parse_instr_fmul(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.fpMul_RNE)


def parse_instr_fadd(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.fpAdd_RNE)


def parse_instr_fsub(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.fpSub_RNE)


def parse_instr_fdiv(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.fpDiv_RNE)


def parse_instr_fneg(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    op = data_token["op1"]
    var_type = data_token["type"]
    value = get_single_value(op, smt_block, var_type)
    res = z3.simplify(z3.fpNeg(value))
    ty = data_token["type"]
    smt_block.add_new_value(value_name, res, ty)


def parse_instr_frem(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3.fpRem)


def parse_instr_udiv(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3.UDiv)


def parse_instr_sdiv(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecSdiv)


def parse_instr_urem(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3.URem)


def parse_instr_srem(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3.SRem)


def parse_instr_and(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecAnd)


def parse_instr_or(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecOr)


def parse_instr_xor(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecXor)


def parse_instr_lshr(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3.LShR)


def parse_instr_ashr(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function(value_name, data_token, smt_block, z3e.BitVecAshr)


def parse_instr_trunc(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    # NOTE: The bit size of the value must be larger than the bit size of the destination type, ty2. Equal sized types are not allowed.
    # Actually the 'trunc' remain the low order bits which means the right side of bits.
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    assert get_type_precision(ty1) > get_type_precision(ty2)
    value = get_single_value(val, smt_block, ty1)
    precision_ty2 = get_type_precision(ty2)
    res = z3.simplify(z3.Extract(precision_ty2, 0, value))
    smt_block.add_new_value(value_name, res, ty2)


def get_ext_smt_result(value, ty1: str, ty2: str, z3_function):
    precision_ty1 = get_type_precision(ty1)
    precision_ty2 = get_type_precision(ty2)
    assert precision_ty2 > precision_ty1
    res = z3.simplify(z3_function(precision_ty2 - precision_ty1, value))
    return res


def parse_instr_zext(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    value = get_single_value(val, smt_block, ty1)
    res = get_ext_smt_result(value, ty1, ty2, z3.ZeroExt)
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_sext(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    value = get_single_value(val, smt_block, ty1)
    res = get_ext_smt_result(value, ty1, ty2, z3.SignExt)
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_conversion(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
    z3_function_conversion,
):
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    value = get_single_value(val, smt_block, ty1)
    sort = get_basic_smt_sort(ty2)
    res = z3.simplify(z3_function_conversion(value, sort))
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_fptrunc(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
):
    # NOTE: The bit size of the value must be larger than the bit size of the destination type, ty2. Equal sized types are not allowed.
    # Actually the 'trunc' remain the low order bits which means the right side of bits.
    # %X = fptrunc double 16777217.0 to float    ; yields float:16777216.0 wrong?
    "Use z3.fpFPToFP to conversion"
    parse_instr_conversion(value_name, data_token, smt_block, z3e.fpFPToFP_RNE)


def parse_instr_fpext(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
):
    # NOTE: The bit size of the value must be larger than the bit size of the destination type, ty2. Equal sized types are not allowed.
    # Actually the 'trunc' remain the low order bits which means the right side of bits.
    # %X = fptrunc double 16777217.0 to float    ; yields float:16777216.0 wrong?
    "Use z3.fpFPToFP to conversion"
    parse_instr_conversion(value_name, data_token, smt_block, z3e.fpFPToFP_RNE)


def parse_instr_fptoui(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    # The ‘fptoui’ instruction converts its floating-point operand into the nearest
    # (rounding towards zero) unsigned integer value. If the value cannot fit in ty2,
    # the result is a poison value.
    parse_instr_conversion(value_name, data_token, smt_block, z3e.fpToUBV_RTZ)


def parse_instr_fptosi(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    # The ‘fptoui’ instruction converts its floating-point operand into the nearest
    # (rounding towards zero) unsigned integer value. If the value cannot fit in ty2,
    # the result is a poison value.
    "The poison value is not implemented!"
    parse_instr_conversion(value_name, data_token, smt_block, z3e.fpToSBV_RTZ)


def parse_instr_uitofp(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_conversion(value_name, data_token, smt_block, z3e.fpUnsignedToFP_RNE)


def parse_instr_sitofp(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_conversion(value_name, data_token, smt_block, z3e.fpSignedToFP_RNE)


def split_argu(argu: str, sp: str):
    tmp = ""
    res = []
    flag: bool = False
    for i in argu:
        if i == sp and flag == False:
            res.append(deepcopy(tmp))
            tmp = ""
        elif i == "<":
            flag = True
            tmp += i
        elif i == ">":
            flag = False
            tmp += i
        else:
            tmp += i
    res.append(tmp)
    return res


def separate_argument(argu: str):
    # FIXME: This part can't handle "<2 x i32> < i32 1, i32 2>, <2 x i32> %a, <2 x i32> %a"
    argu_list = split_argu(argu, ",")
    argu_list = [argu_list[i].strip(" ") for i in range(len(argu_list))]
    pattern = re.compile("(?P<type><.*x.*>|.*?) (?P<val>.*?)$")
    res_argu = []
    for argu_item in argu_list:
        gs = re.search(pattern, argu_item)
        if gs == None:
            raise RuntimeError("The argument is not in our exception..")
        else:
            res_argu.append([gs["type"], gs["val"]])
    return res_argu


def separate_function_and_argument(func_str: str):
    func_str = func_str[1:]
    function_name = func_str.split("(")[0].strip("@")
    arguments = func_str.split("(")[1].strip("(").strip(")")
    return function_name, arguments


def get_smax(a, b):
    return z3.If(a >= b, a, b)


def get_smin(a, b):
    return z3.If(a <= b, a, b)


def get_umax(a, b):
    return z3.If(z3.UGT(a, b), a, b)


def get_umin(a, b):
    return z3.If(z3.ULE(a, b), a, b)


def get_minimum_float(a, b, sort):
    return z3.If(
        z3.Or(z3.fpIsNaN(a), z3.fpIsNaN(b)),
        z3.fpNaN(sort),
        z3.If(
            z3.And(z3.fpIsZero(a), z3.fpIsZero(b)),
            z3.If(
                z3.Or(z3.fpIsNegative(a), z3.fpIsNegative(b)),
                z3.fpMinusZero(sort),
                z3.fpPlusZero(sort),
            ),
            z3.fpMin(a, b),
        ),
    )


def get_maximum_float(a, b, sort):
    return z3.If(
        z3.Or(z3.fpIsNaN(a), z3.fpIsNaN(b)),
        z3.fpNaN(sort),
        z3.If(
            z3.And(z3.fpIsZero(a), z3.fpIsZero(b)),
            z3.If(
                z3.Or(z3.fpIsPositive(a), z3.fpIsPositive(b)),
                z3.fpPlusZero(sort),
                z3.fpMinusZero(sort),
            ),
            z3.fpMax(a, b),
        ),
    )


def get_llvm_compare_result(first, second, func):
    "This function run without type check."
    if isinstance(first, List) and isinstance(second, List):
        assert len(first) == len(second)
        return [func(first[i], second[i]) for i in range(len(first))]
    else:
        return func(first, second)


def parse_instr_llvm_comp(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo, func
):
    argus = separate_argument(argments)
    assert len(argus) == 2
    val_type_first, val_first = argus[0]
    val_type_second, val_second = argus[1]
    first = get_single_value(val_first, smt_block, val_type_first)
    second = get_single_value(val_second, smt_block, val_type_second)
    res = z3.simplify(get_llvm_compare_result(first, second, func))
    smt_block.add_new_value(value_name, res, rs_ty)


def parse_instr_llvm_umax(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_comp(value_name, argments, rs_ty, smt_block, get_umax)


def parse_instr_llvm_umin(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_comp(value_name, argments, rs_ty, smt_block, get_umin)


# TODO: plz check if the smax, umax... just have two arguments once time.
def parse_instr_llvm_smax(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_comp(value_name, argments, rs_ty, smt_block, get_smax)


def parse_instr_llvm_smin(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_comp(value_name, argments, rs_ty, smt_block, get_smin)


def parse_instr_llvm_minnum(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_comp(value_name, argments, rs_ty, smt_block, z3.fpMin)


def parse_instr_llvm_maxnum(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_comp(value_name, argments, rs_ty, smt_block, z3.fpMax)


def parse_instr_llvm_minimum(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    argus = separate_argument(argments)
    assert len(argus) == 2
    val_type_first, val_first = argus[0]
    val_type_second, val_second = argus[1]
    first = get_single_value(val_first, smt_block, val_type_first)
    second = get_single_value(val_second, smt_block, val_type_second)
    assert val_type_first == val_type_second
    sort = get_basic_smt_sort(val_type_first)
    if isinstance(first, List) and isinstance(second, List):
        assert len(first) == len(second)
        res = z3.simplify(
            [get_minimum_float(first[i], second[i], sort) for i in range(len(first))]
        )
    else:
        res = z3.simplify(get_minimum_float(first, second, sort))
    smt_block.add_new_value(value_name, res, rs_ty)


def parse_instr_llvm_maximum(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    argus = separate_argument(argments)
    assert len(argus) == 2
    val_type_first, val_first = argus[0]
    val_type_second, val_second = argus[1]
    first = get_single_value(val_first, smt_block, val_type_first)
    second = get_single_value(val_second, smt_block, val_type_second)
    assert val_type_first == val_type_second
    sort = get_basic_smt_sort(val_type_first)
    if isinstance(first, List) and isinstance(second, List):
        assert len(first) == len(second)
        res = z3.simplify(
            [get_maximum_float(first[i], second[i], sort) for i in range(len(first))]
        )
    else:
        res = z3.simplify(get_maximum_float(first, second, sort))
    smt_block.add_new_value(value_name, res, rs_ty)


def get_abs_result(val):
    if isinstance(val, List):
        a = z3.simplify(z3.Abs(val[0]))
        return [z3.Abs(val[i]) for i in range(len(val))]
    else:
        return z3.Abs(val)


def get_fpabs_result(val):
    if isinstance(val, List):
        return [z3.fpAbs(val[i]) for i in range(len(val))]
    else:
        return z3.fpAbs(val)


def get_sqrt_result_single(val):
    if z3.is_bv_value(val) or z3.is_bv(val):
        return z3.Sqrt(val)
    elif z3.is_fp(val) or z3.is_fp_value(val):
        # TODO: check (For types specified by IEEE-754, the result matches a conforming libm implementation.)
        "Use RNE for fpSqrt now."
        return z3.fpSqrt(z3.RNE(), val)


def get_sqrt_result(val):
    if isinstance(val, List):
        return [get_sqrt_result(val[i]) for i in range(len(val))]
    else:
        return get_sqrt_result(val)


def parse_instr_llvm_single_argument(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo, func
):
    argus = separate_argument(argments)
    assert len(argus) == 1
    ty, val = argus[0][0], argus[0][1]
    value = get_single_value(val, smt_block, ty)
    res = func(value)
    smt_block.add_new_value(value_name, res, rs_ty)


def parse_instr_llvm_abs(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_single_argument(
        value_name, argments, rs_ty, smt_block, get_abs_result
    )


def parse_instr_llvm_fpabs(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_single_argument(
        value_name, argments, rs_ty, smt_block, get_fpabs_result
    )


def get_fpma_result(first, second, third):
    if isinstance(first, List) and isinstance(second, List) and isinstance(third, List):
        assert len(first) == len(second) == len(third)
        return [
            z3.fpFMA(z3.RNE(), first[i], second[i], third[i]) for i in range(len(first))
        ]
    else:
        return z3.fpFMA(z3.RNE(), first, second, third)


def parse_instr_llvm_fma(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    argus = separate_argument(argments)
    assert len(argus) == 3
    val_type_first, val_first = argus[0]
    val_type_second, val_second = argus[1]
    val_type_third, val_third = argus[2]
    first = get_single_value(val_first, smt_block, val_type_first)
    second = get_single_value(val_second, smt_block, val_type_second)
    third = get_single_value(val_third, smt_block, val_type_third)
    res = get_fpma_result(first, second, third)
    smt_block.add_new_value(value_name, res, rs_ty)


def parse_instr_llvm_sqrt(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_single_argument(
        value_name, argments, rs_ty, smt_block, get_sqrt_result
    )


def parse_instr_llvm_llrint(
    value_name: str, argments: str, rs_ty: str, smt_block: st.VerificationInfo
):
    parse_instr_llvm_single_argument(
        value_name, argments, rs_ty, smt_block, get_sqrt_result
    )


def get_powi(number, power):
    "The number must be a float and the"


instr_call_function_dict = {
    "llvm.abs": parse_instr_llvm_abs,
    "llvm.smax": parse_instr_llvm_smax,
    "llvm.umax": parse_instr_llvm_umax,
    "llvm.smin": parse_instr_llvm_smin,
    "llvm.umin": parse_instr_llvm_umin,
    "llvm.sqrt": parse_instr_llvm_sqrt,
    "llvm.fma": parse_instr_llvm_fpabs,
    "llvm.fabs": parse_instr_llvm_fpabs,
    "llvm.minnum": parse_instr_llvm_minnum,
    "llvm.maxnum": parse_instr_llvm_maxnum,
    "llvm.minimum": parse_instr_llvm_minimum,
    "llvm.maximum": parse_instr_llvm_maximum,
    "llvm.llrint": parse_instr_llvm_llrint,
}

# NOTE: These operations are not natively supported by z3.
instr_call_function_dict_unimplemented = {
    "llvm.sin",
    "llvm.cos",
    "llvm.exp",
    "llvm.exp2",
    "llvm.ldexp",
    "llvm.frexp",
    "llvm.log",
    "llvm.log10",
    "llvm.log2",
    "llvm.floor",
    "llvm.ceil",
    "llvm.trunc",
    "llvm.rint",
    "llvm.nearbyint",
    "llvm.round",
    "llvm.roundeven",
    "llvm.lround",
    "llvm.llround",  # TODO: declare i64 @llvm.lround.i64.f80(float %Val) Find wrong in https://llvm.org/docs/LangRef.html#llvm-minimum-intrinsic.
    "llvm.lrin",
    "llvm.llrint",
}


def get_right_key(function_str: str):
    function_slices = function_str.strip().split(".")
    pattern = "llvm"
    for i in range(1, len(function_slices)):
        pattern = pattern + "." + function_slices[i]
        if pattern in instr_call_function_dict.keys():
            return instr_call_function_dict[pattern]
    return None


def parse_instr_call(
    instr: str,
    instr_type: str,
    smt_block: st.VerificationInfo,
    instr_infoDict: Dict | None = None,
):
    """"""
    value_name = instr.split("=")[0].strip(" ")
    if instr_infoDict == None:
        instr_infoDict = get_instr_dict(instr, instr_type)
    assert instr_infoDict != None
    re_type = instr_infoDict["ty"]
    function_all_str = instr_infoDict["function"]
    function_name, argu = separate_function_and_argument(function_all_str)
    parse_function = get_right_key(function_name)
    if parse_function != None:
        parse_function(value_name, argu, re_type, smt_block)


instr_function_simple_dict = {
    "load": parse_instr_load,
    "getelementptr": parse_instr_getelementptr,
    "add": parse_instr_add,
    "sub": parse_instr_sub,
    "mul": parse_instr_mul,
    "shl": parse_instr_shl,
    "udiv": parse_instr_udiv,
    "sdiv": parse_instr_sdiv,
    "urem": parse_instr_urem,
    "srem": parse_instr_srem,
    "and": parse_instr_and,
    "or": parse_instr_or,
    "xor": parse_instr_xor,
    "lshr": parse_instr_lshr,
    "ashr": parse_instr_ashr,
    "icmp": parse_instr_icmp,
    "fadd": parse_instr_fadd,
    "fmul": parse_instr_fmul,
    "frem": parse_instr_frem,
    "fsub": parse_instr_fsub,
    "fdiv": parse_instr_fdiv,
    "fneg": parse_instr_fneg,
    "fcmp": parse_instr_fcmp,
    "trunc": parse_instr_trunc,
    "zext": parse_instr_zext,
    "sext": parse_instr_sext,
    "fptrunc": parse_instr_fptrunc,
    "fpext": parse_instr_fpext,
    "fptoui": parse_instr_fptoui,
    "fptosi": parse_instr_fptosi,
    "uitofp": parse_instr_uitofp,
    "sitofp": parse_instr_sitofp,
}


# TODO: add vscale.
def parse_instr_shufflevector(
    instr: str, smt_block: st.VerificationInfo, data_token: Dict[str, str] | None
):
    def extra_loc_from_mask(mask: str):
        res_list = mask.strip("<").strip(">").strip(" ").split(",")
        mask_res = [
            int(res_list[i].strip().split(" ")[1].strip(" "))
            for i in range(len(res_list))
        ]
        return mask_res

    value_name = re.split("=", instr.strip())[0].strip(" ")
    if data_token == None:
        data_token = get_instr_dict(instr, "shufflevector")

    v1, v2, mask, v1_type, v2_type, v1_size, v2_size, mask_size = (
        data_token["v1"],
        data_token["v2"],
        data_token["v3"],
        data_token["v1_ty"],
        data_token["v2_ty"],
        data_token["v1_n"],
        data_token["v2_n"],
        data_token["mask_n"],
    )

    value_1 = get_single_value(v1, smt_block, vec_ty_example)
    value_2 = get_single_value(v2, smt_block, vec_ty_example)
    assert isinstance(value_1, List) and isinstance(value_2, List)
    value_before = value_1 + value_2
    mask_list = extra_loc_from_mask(mask)
    res_list = []
    for i in mask_list:
        if not (i < len(value_before)):
            raise OverflowError("")
        res_list.append(value_before[i])
    res_ty = "<" + mask_size + " x " + v1_type + ">"
    smt_block.add_new_value(value_name, res_list, res_ty)


instr_function_vector_type_dict = {"shufflevector"}


def parse_instr_two_op_function_v(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
    z3_function_two_op,
):
    first, second = get_ready_two_value_basic(value_name, data_token, smt_block)
    if not is_same_z3_vector_type(first, second):
        raise RuntimeError("The input for z3 vector is not python list!\n")
    assert isinstance(first, List) and isinstance(second, List)
    res = [
        z3.simplify(z3_function_two_op(first[i], second[i])) for i in range(len(first))
    ]
    ty = data_token["type"]
    smt_block.add_new_value(value_name, res, ty)


def parse_instr_add_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecAdd)


def parse_instr_fadd_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.fpAdd_RNE)


def parse_instr_sub_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecSub)


def parse_instr_mul_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecMul)


def parse_instr_shl_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecShl)


def parse_instr_udiv_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3.UDiv)


def parse_instr_sdiv_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecSdiv)


def parse_instr_urem_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3.URem)


def parse_instr_srem_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3.SRem)


def parse_instr_and_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecAnd)


def parse_instr_or_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecOr)


def parse_instr_xor_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecXor)


def parse_instr_lshr_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3.LShR)


def parse_instr_ashr_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.BitVecAshr)


def parse_instr_icmp_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    cond, ty, op1, op2 = (
        data_token["cond"],
        data_token["ty"],
        data_token["op1"],
        data_token["op2"],
    )
    first_value = get_single_value(op1, smt_block, ty)
    second_value = get_single_value(op2, smt_block, ty)
    assert isinstance(first_value, List)
    assert isinstance(second_value, List)
    res = [
        get_icmp_result(first_value[i], second_value[i], cond)
        for i in range(len(first_value))
    ]
    smt_block.add_new_value(value_name, res, "i1")


def parse_instr_fmul_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.fpMul_RNE)


def parse_instr_frem_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3.fpRem)


def parse_instr_fsub_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3e.fpSub_RNE)


def parse_instr_fdiv_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    parse_instr_two_op_function_v(value_name, data_token, smt_block, z3.fpDiv)


def parse_instr_fneg_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    op = data_token["op1"]
    var_type = data_token["type"]
    value = get_single_value(op, smt_block, var_type)
    assert isinstance(value, List)
    res = [z3.simplify(z3.fpNeg(value[i])) for i in range(len(value))]
    ty = data_token["type"]
    smt_block.add_new_value(value_name, res, ty)


def parse_instr_fcmp_vec(
    value_name: str, data_token: Dict, smt_block: st.VerificationInfo
):
    ordered_group = {"oeq", "ogt", "oge", "olt", "ole", "one", "ord"}
    unordered_group = {"ueq", "ugt", "uge", "ult", "ule", "une", "uno"}
    cond, ty, op1, op2 = (
        data_token["cond"],
        data_token["ty"],
        data_token["op1"],
        data_token["op2"],
    )
    first_value = get_single_value(op1, smt_block, ty)
    second_value = get_single_value(op2, smt_block, ty)
    assert isinstance(first_value, List)
    assert isinstance(second_value, List)
    res = [
        get_fcmp_result(first_value[i], second_value[i], cond)
        for i in range(len(first_value))
    ]
    smt_block.add_new_value(value_name, res, "i1")


def parse_instr_trunc_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    # NOTE: The bit size of the value must be larger than the bit size of the destination type, ty2. Equal sized types are not allowed.
    # Actually the 'trunc' remain the low order bits which means the right side of bits.
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    assert is_vec_type(ty1) and is_vec_type(ty2)
    ty1_var_size, ty1_var_type = get_info_from_vector_type(ty1)
    ty2_var_size, ty2_var_type = get_info_from_vector_type(ty2)
    assert get_type_precision(ty1_var_type) > get_type_precision(ty2_var_type)
    value = get_single_value(val, smt_block, ty1)
    precision_ty2 = get_type_precision(ty2_var_type)
    assert isinstance(value, List)
    res = [
        z3.simplify(z3.Extract(precision_ty2, 0, value[i])) for i in range(len(value))
    ]
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_zext_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    assert is_vec_type(ty1) and is_vec_type(ty2)
    ty1_var_size, ty1_var_type = get_info_from_vector_type(ty1)
    ty2_var_size, ty2_var_type = get_info_from_vector_type(ty2)
    value = get_single_value(val, smt_block, ty1)
    assert isinstance(value, List)
    assert ty1_var_size == ty2_var_size
    res = [
        get_ext_smt_result(value[i], ty1_var_type, ty2_var_type, z3.ZeroExt)
        for i in range(len(value))
    ]
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_sext_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    assert is_vec_type(ty1) and is_vec_type(ty2)
    ty1_var_size, ty1_var_type = get_info_from_vector_type(ty1)
    ty2_var_size, ty2_var_type = get_info_from_vector_type(ty2)
    value = get_single_value(val, smt_block, ty1)
    assert isinstance(value, List)
    assert ty1_var_size == ty2_var_size
    res = [
        get_ext_smt_result(value[i], ty1_var_type, ty2_var_type, z3.SignExt)
        for i in range(len(value))
    ]
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_conversion_vec(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
    z3_function_conversion,
):
    ty1, val, ty2 = {data_token["ty1"], data_token["val"], data_token["ty2"]}
    assert is_vec_type(ty1) and is_vec_type(ty2)
    ty1_var_size, ty1_var_type = get_info_from_vector_type(ty1)
    ty2_var_size, ty2_var_type = get_info_from_vector_type(ty2)
    value = get_single_value(val, smt_block, ty1_var_type)
    sort = get_basic_smt_sort(ty2_var_type)
    assert isinstance(value, List)
    assert ty1_var_size == ty2_var_size
    res = [
        z3.simplify(z3_function_conversion(value[i], sort)) for i in range(len(value))
    ]
    smt_block.add_new_value(value_name, res, ty2)


def parse_instr_fptrunc_vec(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
):
    "Use z3.fpFPToFP to conversion"
    parse_instr_conversion_vec(value_name, data_token, smt_block, z3e.fpFPToFP_RNE)


def parse_instr_fpext_vec(
    value_name: str,
    data_token: Dict[str, str],
    smt_block: st.VerificationInfo,
):
    "Use z3.fpFPToFP to conversion"
    parse_instr_conversion_vec(value_name, data_token, smt_block, z3e.fpFPToFP_RNE)


def parse_instr_fptoui_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_conversion_vec(value_name, data_token, smt_block, z3e.fpToUBV_RTZ)


def parse_instr_fptosi_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    # The ‘fptoui’ instruction converts its floating-point operand into the nearest
    # (rounding towards zero) unsigned integer value. If the value cannot fit in ty2,
    # the result is a poison value.
    "The poison value is not implemented!"
    parse_instr_conversion_vec(value_name, data_token, smt_block, z3e.fpToSBV_RTZ)


def parse_instr_uitofp_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_conversion_vec(
        value_name, data_token, smt_block, z3e.fpUnsignedToFP_RNE
    )


def parse_instr_sitofp_vec(
    value_name: str, data_token: Dict[str, str], smt_block: st.VerificationInfo
):
    parse_instr_conversion_vec(value_name, data_token, smt_block, z3e.fpSignedToFP_RNE)


instr_function_vector_dict = {
    "load": parse_instr_load,
    "add": parse_instr_add_vec,
    "sub": parse_instr_sub_vec,
    "mul": parse_instr_mul_vec,
    "shl": parse_instr_shl_vec,
    "udiv": parse_instr_udiv_vec,
    "sdiv": parse_instr_sdiv_vec,
    "urem": parse_instr_urem_vec,
    "srem": parse_instr_srem_vec,
    "and": parse_instr_and_vec,
    "or": parse_instr_or_vec,
    "xor": parse_instr_xor_vec,
    "lshr": parse_instr_lshr_vec,
    "ashr": parse_instr_ashr_vec,
    "icmp": parse_instr_icmp_vec,
    "fadd": parse_instr_fadd_vec,
    "fmul": parse_instr_fmul_vec,
    "frem": parse_instr_frem_vec,
    "fsub": parse_instr_fsub_vec,
    "fdiv": parse_instr_fdiv_vec,
    "fneg": parse_instr_fneg_vec,
    "fcmp": parse_instr_fcmp_vec,
    "trunc": parse_instr_trunc_vec,
    "zext": parse_instr_zext_vec,
    "sext": parse_instr_sext_vec,
    "fptrunc": parse_instr_fptrunc_vec,
    "fpext": parse_instr_fpext_vec,
    "fptoui": parse_instr_fptoui_vec,
    "fptosi": parse_instr_fptosi_vec,
    "uitofp": parse_instr_uitofp_vec,
    "sitofp": parse_instr_sitofp_vec,
}


def is_no_return_instr(instr_type: str):
    return True if instr_type == "store" else False


def parse_instr_no_return():
    pass


def is_vectortype_instr(instr_type: str):
    if instr_type in instr_function_vector_type_dict:
        return True
    else:
        return False


def is_call_instr(instr_type: str):
    if instr_type in call_type:
        return True
    else:
        return False


def get_type_from_dict_token(token: Dict):
    keys = token.keys()
    if "type" in keys:
        return token["type"]
    elif "ty" in keys:
        return token["ty"]
    elif "ty1" in keys:
        return token["ty1"]
    else:
        raise RuntimeError("There is no type in token.keys!\n")


def is_vectortype_basedon_dict_token(token: Dict, instr, instr_type):
    keys = token.keys()

    if instr_type in getelementptr_type:
        return False

    if "type" in keys:
        return is_vec_type(token["type"])
    elif "ty" in keys:
        return is_vec_type(token["ty"])
    elif "ty1" in keys:
        return is_vec_type(token["ty1"])
    else:
        raise RuntimeError(
            "There is no type in token.keys!.\n The instr is {}.\n".format(instr)
        )


def get_instr_dict(instr: str, instr_type: str):
    slice = instr.strip()
    if instr_type not in NO_RETURN:
        slice = re.split("=", slice)[1].strip(" ")
    slice_token_math = extra_slice_token(slice, instr_type)
    if slice_token_math == None:
        raise RuntimeError("The instr({}) dict token is None!".format(instr))
    return slice_token_math.groupdict()


def parse_instr_basic(
    instr: str,
    instr_type: str,
    smt_block: st.VerificationInfo,
    instr_infoDict: Dict | None = None,
):
    instr = instr.strip()
    name = re.split("=", instr)[0].strip(" ")
    if instr_infoDict == None:
        instr_infoDict = get_instr_dict(instr, instr_type)
    if instr_type in instr_function_simple_dict.keys():
        instr_function_simple_dict[instr_type](name, instr_infoDict, smt_block)
    else:
        raise st.NotImplementedError("The instr({}) is not implemented".format(instr))


def parse_instr_vector(
    instr: str,
    instr_type: str,
    smt_block: st.VerificationInfo,
    instr_infoDict: Dict | None = None,
):
    instr = instr.strip()
    name = re.split("=", instr)[0].strip(" ")
    if instr_infoDict == None:
        instr_infoDict = get_instr_dict(instr, instr_type)
    if instr_type in instr_function_vector_dict.keys():
        instr_function_vector_dict[instr_type](name, instr_infoDict, smt_block)
    else:
        raise st.NotImplementedError("The instr is not implemented")


# TODO: add filter.
def parse_instr(instr: str, instr_type: str, smt_block: st.VerificationInfo):
    instr_info_dict = get_instr_dict(instr, instr_type)
    if is_no_return_instr(instr_type):
        parse_instr_no_return()
    elif is_vectortype_instr(instr_type):
        parse_instr_shufflevector(instr, smt_block, instr_info_dict)
    elif is_call_instr(instr):
        parse_instr_call(instr, instr_type, smt_block, instr_info_dict)
    else:
        if not is_vectortype_basedon_dict_token(instr_info_dict, instr, instr_type):
            parse_instr_basic(instr, instr_type, smt_block, instr_info_dict)
        else:
            parse_instr_vector(instr, instr_type, smt_block)


def generate_instr_types(instrs: List[str]) -> List[str]:
    instr_types = []
    for line in instrs:
        find_flag = False
        for word in re.split(" ", line):
            if word in CARE_OPCODE:
                instr_types.append(word)
                find_flag = True
                break
        if find_flag == False:
            raise st.NotImplementedError(
                "Can't find the type for this instr: {}.".format(line)
            )

    return instr_types


def parse_instrs(
    instrs: List[str], instr_types: List[str], smt_block: st.VerificationInfo
):
    if len(instr_types) != len(instrs):
        instr_types = generate_instr_types(instrs)
        if len(instr_types) != len(instrs):
            raise RuntimeError("Can't fit the size of instrs and its type!")
    for i in range(0, len(instrs)):
        instr = instrs[i]
        type = instr_types[i]
        parse_instr(instr, type, smt_block)
