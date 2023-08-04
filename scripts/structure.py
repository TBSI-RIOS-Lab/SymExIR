from enum import Enum
from typing import Dict, List

import llvmlite.binding as llvm
import z3
from config import *
from util import get_instr_dict, get_instr_type, get_instr_value_name

uninplement_instr = [
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
    "phi",
    "select",
    "fence",
    "phi",
    "select",
    "freeze",
    "call",
    "va_arg",
    "landingpad",
    "catchpad",
    "cleanuppad",
]


class NotImplementedError(Exception):
    """Raised when encountering unimplemented part."""

    def __init__(self, string: str, location=None):
        self.location = location
        Exception.__init__(self, string)


class Error(Exception):
    """Raised when being passed incorrect input, etc."""

    def __init__(self, string, location=None):
        self.location = location
        Exception.__init__(self, string)


class SmtPointer:
    def __init__(self, mem_id, offset):
        assert mem_id.sort() == z3.BitVecSort(PTR_ID_BITS)
        assert offset.sort() == z3.BitVecSort(PTR_OFFSET_BITS)
        self.mem_id = mem_id
        self.offset = offset

    def bitvector(self):
        return z3.Concat([self.mem_id, self.offset])


class DataType(Enum):
    """Enum type for data."""

    RealType = 1
    BooleanType = 2
    IntegerType = 3
    FloatingType = 4
    VectorType = 5


class Var:
    """"""

    def __init__(
        self, data_type: str, value_name: str, real_value, is_immediate: bool = False
    ) -> None:
        self._data_type: str = data_type
        self._immediate: bool = is_immediate
        if is_immediate == True:
            self._value_name = value_name
            self._real_value = (
                None  # The type of real_value in python(int or float ..) is not sure.
            )
        else:
            self._value_name = None
            self._real_value = real_value


class Instruction:
    """Contain all the data to represent an instruction"""

    def __init__(
        self, opcode: str, operators: list, data_type: str, return_value
    ) -> None:
        self._opcode: str = opcode
        self._operators: list = operators
        self._data_type = str()
        self._return_value = return_value


class LoadAssertInfo:
    """"""

    def __init__(self, assertValue_list: List[tuple]) -> None:
        self._loc2_value: Dict[int, str] = dict()
        for i in range(len(assertValue_list)):
            pair = assertValue_list[i]
            self._loc2_value[pair[0]] = pair[1]

    def __str__(self) -> str:
        res = ""
        for item in self._loc2_value:
            res += str(item) + "," + str(self._loc2_value[item])
            res += "  "
        return res

    @property
    def loc_value(self):
        return self._loc2_value

    def get_value_str(self, loc):
        return self.loc_value[loc]


class VerificationLaodInfo:
    """Contain all information before the."""

    def __init__(self, instrs, load_info) -> None:
        self._class_name = "VerificationLaodInfo"
        self._instrs = instrs
        self._load_info = load_info
        self._loc2_instrDict = list()
        self._loc2_instrValueName = list()
        self._valueName2_loc = dict()
        self._loc2_instrType = list()
        for i in range(len(instrs)):
            instr_type = get_instr_type(self.instrs[i])
            self._loc2_instrType.append(instr_type)
            self._loc2_instrDict.append(get_instr_dict(self.instrs[i]))
            value_name = get_instr_value_name(self.instrs[i], instr_type)
            self._loc2_instrValueName.append(value_name)
            self._valueName2_loc[value_name] = i

    @property
    def instrs(self):
        return self._instrs

    @property
    def loc2_instrDict(self):
        return self._loc2_instrDict

    @property
    def valueName2_loc(self):
        return self._valueName2_loc

    @property
    def loc2_instrType(self):
        return self._loc2_instrDict

    def get_instr_type(self, loc):
        return self.loc2_instrType[loc]

    def get_instr_dict(self, instr_loc):
        return self.loc2_instrDict[instr_loc]


class SmtBlockBasic:
    """Contain smt list for smt-solver execution."""

    def __init__(self):
        self.verification_list = []
        self.list = []


class VerificationContext:
    """Contain all information for the verification of one process."""

    def __init__(self) -> None:
        self.var2list: Dict[str, int] = {}
        self.smt_list: List = []
        self.var2type: Dict[str, str] = {}

    def add_new_value(self, name: str, value, type):
        if name in self.var2list.keys():
            return
        self.smt_list.append(z3.simplify(value))
        self.var2list[name] = len(self.smt_list) - 1
        self.var2type[name] = type

    def find_value_by_name(self, name: str):
        if name not in self.var2list.keys():
            raise ValueError("There is no value({}) you want.".format(name))
        loc = self.var2list[name]
        return self.smt_list[loc]

    def get_value_type_by_name(self, name: str):
        if name not in self.var2type.keys():
            raise ValueError("There is no value({}) you want.".format(name))
        return self.var2type["name"]
    
    def is_there_same_value(self, name: str) -> bool:
        if name in self.var2list.keys():
            return True
        return False

    def dump(self):
        for key in self.var2list.keys():
            loc = self.var2list[key]
            print(str(self.smt_list[loc]))

    def dump_with_type(self):
        for key in self.var2list.keys():
            loc = self.var2list[key]
            print(str(self.smt_list[loc]), self.var2type[key])

    def repalce_new_value(self, name: str, value):
        list_loc = self.var2list[name]
        self.smt_list[list_loc] = value

    def replace_or_insert_new_value(self, name: str, value, type):
        if name in self.var2list.keys():
            self.add_new_value(name, value, type)
        else:
            self.repalce_new_value(name, value)


class VectorTypeInfo:
    def __init__(self, size: int, type: str) -> None:
        self._size = size
        self._type = type

    @property
    def size(self):
        return self._size

    @property
    def type(self):
        return self._type
