import argparse
import sys

import structure as st
import verify as vf

parser = argparse.ArgumentParser()
parser.add_argument("--instrfile", help="To specify llvm instrs file path")
parser.add_argument("--assertfile", help="To specify assert info file path")
parser.add_argument(
    "--dumpinfo", action="store_true", help="To dump the info from verify proccess"
)
parser.add_argument("--generateResult", action="store_true",help="To generate the calculate result")

args = parser.parse_args()

if __name__ == "__main__":
    instr_path = args.instrfile
    assert_path = args.assertfile
    if instr_path is None or assert_path is None:
        print("Plz provide a right path for verify!")
        sys.exit(1)
    verify_info = st.get_verificationloadinfo_from_file(instr_path, assert_path)
    load_info = st.get_verifyInfo_from_file(assert_path)
    if args.generateResult:
        res_smt = vf.generate_calculate_result(verify_info, load_info)
        print(res_smt.value_str_pretty())
    else:
        res_smt = vf.verify(verify_info, load_info)
        print("Verify success!")
        if args.dumpinfo:
            res_smt.dump_with_valueName_type()
