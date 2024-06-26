#! /bin/sh

import os
import glob
import subprocess
from typing import List

BENCHMARK_FOLDER = "benchmarks"
OUTPUT_PATH = "test_output.txt"


def check_sat(end_sys: str) -> bool:
    """
    Checks the satisfiability based on the saved output file
    """
    sat = "UNDEF"
    if not isinstance(end_sys, str):
        print("End system is undefined!!")
        return sat
    
    with open(f"{end_sys}_output.txt", "r") as file:
        lines = file.readlines()
        for line in lines:
            if line.startswith(("Answer", "SAT", "SATISFIABLE")):
                sat = True
                break
            elif line.startswith("UNSAT"):
                sat = False
                break
    return sat
    

def main():
    if os.path.exists(OUTPUT_PATH):
        os.remove(OUTPUT_PATH)

    for folder in glob.glob(f"{BENCHMARK_FOLDER}/*"):
        if not folder.endswith("blending"):
            continue
        for script in glob.glob(f"{folder}/encodings/*.con"):
            for instance in glob.glob(f"{folder}/instances/*"):
                end_sys = "clingoLP"
                # command = f"{end_sys} {folder}/encodings/ezsmt.lp {script} {instance}"
                # command += f" -q 1"
                command = f"{end_sys} {script} {instance}"
                print(command)
                with open(f"{end_sys}_output.txt", "w") as file:
                    subprocess.run([command], shell=True, stdout=file, stderr=file)
                sat = check_sat(end_sys)

                subprocess.run([f"echo \"{sat} {script} {instance}\" >> {OUTPUT_PATH}"], shell=True)

if __name__ == "__main__":
    main()
            
