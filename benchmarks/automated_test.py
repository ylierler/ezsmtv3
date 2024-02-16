#! /bin/sh

import os
import glob
import subprocess
from typing import List

BENCHMARK_FOLDER = "ezsmtPlus_benchmarks"

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

def get_eval(sat_list: List[str]):
    """
    Compares and evaluates the sat list returned by the systems
    """
    sat_1, sat_2 = sat_list
    evaluation = "OKAY" if sat_1==sat_2 else "NOT-OKAY"   
    sat_str = "SAT" if sat_1==True else "UNSAT"
    sat_str += " SAT" if sat_2==True else " UNSAT"    
    return evaluation, sat_str

def main():
    if os.path.exists("output.txt"):
        os.remove("output.txt")

    for folder in glob.glob(f"{BENCHMARK_FOLDER}/*"):
        if not folder.endswith("generator"):
            continue
        for script in glob.glob(f"{folder}/encodings/*.con"):
            for instance in glob.glob(f"{folder}/instances/*"):        
                # end_systems =["ezsmt", "clingcon"]                                # for ezsmt and clingcon
                end_systems = ["ezsmt", "clingoLP"]                                 # for ezsmt and clingLP
                
                end_sys = end_systems[0]
                command = f"{end_sys} {script} {instance}"
                command += f" -d debug.lp"
                command += f" -q 1"                                                 # for ezsmt and clingLP
                print(command)
                with open(f"{end_sys}_output.txt", "w") as file:
                    subprocess.run([command], shell=True, stdout=file, stderr=file)
                ez_sat = check_sat(end_sys)
                
                end_sys = end_systems[1]
                # command = f"{end_sys} {script} {instance}"                        # for ezsmt and clingcon
                command = f"{end_sys} 0 --show-lp-solution {script} {instance}"     # for ezsmt and clingLP
                
                if ez_sat:
                    command += " debug.lp"
                print(command)
                with open(f"{end_sys}_output.txt", "w") as file:
                    subprocess.run([command], shell=True, stdout=file, stderr=file)
                con_sat = check_sat(end_sys)

                evaluation, sat_str = get_eval([ez_sat, con_sat])
                subprocess.run([f"echo \"{evaluation} {sat_str} {script} {instance}\" >> output.txt"], shell=True)

if __name__ == "__main__":
    main()
            
