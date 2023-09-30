import operator as opt
from typing import List, Set

import regex as re
import z3
from utilComputeFunc import normalizedFloatingPoint_to_Decimal

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

NO_RETURN = {"store", "fence"}

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
}

""""
    Only support the most basic edtion just like:
    <result> = extractvalue {i32, float} %agg, 0
    %agg1 = insertvalue {i32, float} undef, i32 1, 0
"""
extractvalue_type = {"extractvalue"}
insertvalue_type = {"insertvalue"}
icmp_group = {"icmp"}
fcmp_group = {"fcmp"}
select_type = {"select"}
over_bb_group = {
    "phi",
    "va_arg",
    "landingpad",
    "catchpad",
    "cleanuppad",
}  # TODO: add description of getelementptr in document

fence_instr_group = {"fence"}
memory_group = {"cmpxchg", "atomicrmw"}
store_type = {
    "store"
}  # Actually for now the "store" is meaningless for the whole program, but we still finish that.
alloca_type = {"alloca"}
load_type = {"load"}
call_type = {"call"}
getelementptr_type = {"getelementptr"}
llvm_instr = {"llvm.minnum"}

# TODO: add ptr
ptr_instr_group = {"ptrtoint", "bitcast", "inttoptr", "addrspacecast"}

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
            "^extractelement "
            + "<((?P<vs>.*?) x ){0,1}(?P<n>.*?) x (?P<ty>.*?)> (?P<val><.*?>|.*?)"
            + ", "
            + "(?P<ty1>.*?) (?P<op1>.*?)"
            + "$"
        )

    elif instr_type in insertelement_type:
        pattern = re.compile(
            "^insertelement "
            + "<((?P<vs>.*?) x ){0,1}(?P<n>.*?) x (?P<ty>.*?)> (?P<val><.*?>|.*?)"
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

    elif instr_type in extractvalue_type:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(?P<type>{.*?}) "
            + "(?P<op_val>.*?), "
            + "(?P<idx>.*?)"
            + "$"
        )

    elif instr_type in insertvalue_type:
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(?P<type>{.*?}) "
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
            + "(?P<selty><.*?x.*?>|.*?) "
            + "(?P<cond><.*?>|.*?), (?P<ty1><.*? x .*?>|.*?) (?P<op1><.*>|.*?), (?P<ty2><.*? x .*?>|.*?) (?P<op2><.*>|.*?)$"
        )

    elif instr_type in fence_instr_group:
        pattern = re.compile("")
    elif instr_type in memory_group:
        # %old = atomicrmw add ptr %ptr, i32 1 acquire
        if instr_type == "atomicrmw":
            pattern = re.compile("^" + instr_type + ".*?, " + "(?P<ty>.*?) " + ".*?$")
        # %val_success = cmpxchg ptr %ptr, i32 %cmp, i32 %squared acq_rel monotonic
        elif instr_type == "cmpxchg":
            pattern = re.compile("^" + instr_type + ".*?, " + "(?P<ty>.*?) " + ".*?$")

    elif instr_type in ptr_instr_group:
        # %X = ptrtoint ptr %P to i8
        # %Z = ptrtoint <4 x ptr> <ptr 1, ptr 1, ptr 1, ptr 1> to <4 x i64>
        if instr_type == "ptrtoint":
            pattern = re.compile(
                "^"
                + instr_type
                + " (?P<ptr_ty><.*? x .*?>|.*?) (?P<ptr_val><.*? x .*?>|.*?) to "
                + "(?P<ty><.*? x .*?>|.*?)$"
            )
        # %X = inttoptr i32 255 to ptr
        # %Z = inttoptr <4 x i32> <i32 1, i32 1, i32 1, i32 1> to <4 x ptr>
        elif instr_type == "inttoptr":
            pattern = re.compile(
                "^"
                + instr_type
                + " (?P<ty><.*? x .*?>|.*?) (?P<val><.*? x .*?>|.*?) to "
                + "(?P<ptr_ty><.*? x .*?>|.*?)"
                + "(,.*?){0,1}$"
            )
        # %Y = bitcast i32* %x to i16*
        # %Z = bitcast <2 x i32*> %V to <2 x i64*>
        elif instr_type == "bitcast":
            pattern = re.compile(
                "^"
                + instr_type
                + " (?P<ptr_ty><.*? x .*?>|.*?) (?P<val><.*? x .*?>|.*?) to "
                + "(?P<ty><.*? x .*?>|.*?)$"
            )
        # %X = addrspacecast ptr %x to ptr addrspace(1)
        # %Z = addrspacecast <4 x ptr> %z to <4 x ptr addrspace(3)>
        elif instr_type == "addrspacecast":
            pattern = re.compile(
                "^" + instr_type + " (?P<ptr_ty><.*? x .*?>|.*?) .*? to " + ".*?$"
            )

    elif instr_type in store_type:
        # The type of the <pointer> operand must be a pointer to the first class type of the <value> operand
        pattern = re.compile(
            "^"
            + instr_type
            + " "
            + "(atomic ){0,1}"
            + "(volatile ){0,1}"
            + "(?P<ty><.*x.*>|.*?) "
            + "(?P<value><.*x.*>|.*?), (?P<ptr_ty><.*x.*>|.*?) "
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

    if pattern is not None:
        gs = re.search(
            pattern,
            token_ex,
        )
        return gs


def get_instr_value_name(instr: str, instr_type: str):
    if instr_type not in NO_RETURN:
        return re.split("=", instr)[0].strip(" ")
    else:
        return "NoValueName"


def is_instr_in_memory_group(instr_type):
    return True if instr_type in memory_group else False


def is_instr_in_ptr_instr_group(instr_type):
    return True if instr_type in ptr_instr_group else False


def is_instr_over_bb(instr_type):
    return True if instr_type in over_bb_group else False


def is_no_return_instr(instr_type: str):
    return True if instr_type in NO_RETURN else False


def is_termanitor_instr_type(instr_type):
    return True if instr_type in terminator_instr_group else False


def get_instr_dict(instr: str, instr_type: str):
    slice = instr.strip()
    if instr_type not in NO_RETURN:
        slice = re.split("=", slice)[1].strip(" ")
    slice_token_math = extra_slice_token(slice, instr_type)
    if slice_token_math is None:
        raise RuntimeError("The instr({}) dict token is None!".format(instr))
    return slice_token_math.groupdict()


def get_instr_type(instr: str) -> str:
    find_flag = False
    for word in re.split(" ", instr):
        if word in CARE_OPCODE:
            return word
    if find_flag is False:
        raise NotImplementedError(
            "Can't find the type for this instr: {}.".format(instr)
        )


def generate_instr_types(instrs: List[str]) -> List[str]:
    instr_types = []
    for line in instrs:
        instr_types.append(get_instr_type(line))
    return instr_types


no_assert_group = {
    # Terminator Instructions
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
    "freeze",
    "phi",
    "va_arg",
    "landingpad",
    "catchpad",
    "cleanuppad",
    # Aggregate Operations
    "insertvalue",
    "extractvalue",
    # Memory Access and Addressing Operations
    "load",
    "store",
    "alloca",
    "fence",
    "cmpxchg",
    "atomicrmw",
    "getelementptr",
    # other operation
}

ret_aggregate_instr_group = {"extractelement"}


constraint_instr_type = {"load", "getelementptr", "extractvalue"}


def no_assertion_value(instr_type) -> bool:
    return (
        True
        if (instr_type in ret_aggregate_instr_group) or (instr_type in NO_RETURN)
        else False
    )


def is_assert_instr_type(instr_type: str) -> bool:
    return False if instr_type in no_assert_group else True


def is_constraint_type(instr_type: str) -> bool:
    return True if instr_type in constraint_instr_type else False


# def get_instr_return_type(instr: str, instr_type: str, instr_info: Dict) -> str:
#     if instr_info == None:
#         instr_info = get_instr_dict(instr)

#     if instr_type in terminator_instr_group:
#         return ""
#     elif instr_type in regular_group:
#         return instr_info["type"]

#     elif instr_type in flaot_group:
#         return instr_info["type"]

#     elif instr_type in extact_flag_group:
#         return instr_info["type"]

#     elif instr_type in type_twoop_orv_group:
#         return instr_info["type"]

#     elif instr_type in unary_flaot_operators:
#         return instr_info["type"]

#     elif instr_type in extractelement_type:
#         return instr_info["ty"]

#     elif instr_type in insertelement_type:
#         res_str = "<" + str(instr_info["n"]) + " x " + str(instr_info["ty"]) + ">"
#         return res_str

#     elif instr_type in shufflevector_type:
#         # No vscale are in our consideration.
#         res_str = "<" + str(instr_info["v1_n"]) + " x " + str(instr_info["v1_ty"]) + ">"
#         return res_str

#     elif instr_type in conversion_operations_group:
#         return instr_info["ty2"]


def is_vec_type(value_type: str):
    if value_type.startswith("<"):
        return True
    else:
        return False


def get_vector_inner_type(value_type: str):
    if not is_vec_type(value_type):
        raise RuntimeError("Must be vector type!")
    v_type = value_type.strip("<").strip(">")
    v_type = v_type.split("x")[-1].strip()
    return v_type


def is_number(string):
    pattern = re.compile(r"^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$")
    return bool(pattern.match(string))


def is_care_opcode(s: str) -> bool:
    return True if s in CARE_OPCODE else False


def is_aggregate_operations(instr_type: str):
    return (
        True
        if instr_type in extractvalue_type or instr_type in insertvalue_type
        else False
    )


def is_call_type(instr_type: str):
    return True if instr_type in call_type else False


def is_vec_smt_type(value_type: str):
    pattern = r"^<\d x (?P<type>\S*)>$"
    match = re.match(pattern, value_type)
    return match is not None


def pretty_smt_list(smt_type: str, value: List[str]):
    """Print the list in smt better.
    just like < i32 123, i32 3244, i32 999>."""
    pattern = r"^<\d x (?P<type>\S*)>$"
    match = re.match(pattern, smt_type)
    if match is None:
        raise ValueError(f"The input({smt_type}) is not a vec type")
    single_value_type = match.groupdict()["type"]
    res_str = "< "
    for single_value in value:
        res_str += single_value_type + " " + single_value + ", "
    if res_str.endswith(", "):
        res_str = res_str[:-2]
    res_str += ">"
    return res_str


def get_normal_str_from_z3_type(source) -> str | None:
    """Return the basic mode in normal literal way."""
    if isinstance(source, z3.FPNumRef):
        return str(normalizedFloatingPoint_to_Decimal(str(source)))
    elif isinstance(source, z3.BitVecNumRef):
        return str(source)
    else:
        raise RuntimeError(
            f"Plz add the normal str way of {type(source)} before use the function"
        )
