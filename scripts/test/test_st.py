import regex as re
import sys

sys.path.append("..")

from structure import *


def test_load():
    l = [(1, "1"), (2, "1")]
    load = LoadAssertInfo(l)
    print(str(load))


if __name__ == "__main__":
    test_load()
