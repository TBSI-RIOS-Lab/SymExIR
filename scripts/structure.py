from enum import Enum
from typing import Dict, List

import llvmlite.binding as llvm
import z3
from config import *

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


class VerificationLaodInfo:
    """Contain all information before the."""

    def __init__(self) -> None:
        self.class_name = "VerificationLaodInfo"


class SmtBlockBasic:
    """Contain smt list for smt-solver execution."""

    def __init__(self):
        self.verification_list = []
        self.list = []


class VerificationInfo:
    """Contain all information for the verification of one process."""

    def __init__(self) -> None:
        self.var2list: Dict[str, int] = {}
        self.smt_list: List = []
        self.var2type: Dict[str, str] = {}

    def add_new_value(self, name: str, value, type):
        self.smt_list.append(value)
        self.var2list[name] = len(self.smt_list) - 1
        self.var2type[name] = type

    def find_value_by_name(self, name: str):
        if name not in self.var2list.keys():
            raise ValueError("There is no value({}) you want.".format(name))
        loc = self.var2list[name]
        return self.smt_list[loc]

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
