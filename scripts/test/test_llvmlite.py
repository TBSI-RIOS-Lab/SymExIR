import llvmlite.binding as llvm
import llvmlite.ir as ir


def test_read_file():
    with open("add_test.ll", "r+") as f:
        file = f.read()
        try:
            module = llvm.parse_assembly(file)
            module.verify()
            for function in module.functions:
                for bb in function.blocks:
                    for instr in bb.instructions:
                        s = str(instr.type)
                        print(s)
                        print(instr.opcode)
        except RuntimeError:
            print("parse ir file fail, the file name is" + file)


if __name__ == "__main__":
    test_read_file()
