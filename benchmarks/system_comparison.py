#! /bin/sh

import os
import gc
import glob
import subprocess
from typing import List

BENCHMARK_FOLDER = "random"

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

def prepare_debug_file():
    with open("clingcon_output.txt", "r") as file:
        lines = file.readlines()
        atoms_flag, assignments_flag = False, False
        # as_bool_idx = 4
        # as_int_idx = 6
        for idx, line in enumerate(lines):
            if "answer" in line.lower():
                atoms_idx = idx + 1
                atoms_flag = True
            elif "assignment" in line.lower():
                assignments_idx = idx + 1
                assignments_flag = True
            if atoms_flag and assignments_flag:
                break
                
        as_bool = lines[atoms_idx]
        atoms = as_bool.split()
        as_int = lines[assignments_idx]
        assignments = as_int.split()
    
    with open("debug.lp", "w") as file:
        for atom in atoms:
            file.write(f":- not {atom}.\n")
        for assignment in assignments:
            variable, value = assignment.split("=")
            writable = "&sum{" + variable + "} = " + value + ".\n"
            file.write(writable)    

def compare_ezsmt_to_others(folder, script, instance):
    end_systems =["ezsmt", "clingcon"]                                # for ezsmt and clingcon
    # end_systems = ["ezsmt", "clingoLP"]                                 # for ezsmt and clingoLP
    try:
        end_sys = end_systems[0]
        command = f"{end_sys} {script} {instance}"
        # command = f"{end_sys} {folder}/encodings/theory.lp {script} {instance}"
        command += f" -d debug.lp"
        # command += "--solver z3"
        # command += f" -q 1"                                                 # for ezsmt and clingoLP
        print(command)
        with open(f"{end_sys}_output.txt", "w") as file:
            subprocess.run([command], shell=True, stdout=file, stderr=file, timeout=15)
            gc.collect()
        ez_sat = check_sat(end_sys)
        
        end_sys = end_systems[1]
        command = f"{end_sys} {script} {instance}"                        # for ezsmt and clingcon
        # command = f"{end_sys} 0 --show-lp-solution {script} {instance}"     # for ezsmt and clingoLP
        
        if ez_sat:
            command += " debug.lp"
        print(command)
        with open(f"{end_sys}_output.txt", "w") as file:
            subprocess.run([command], shell=True, stdout=file, stderr=file, timeout=15)
            gc.collect()
        con_sat = check_sat(end_sys)

        evaluation, sat_str = get_eval([ez_sat, con_sat])
        subprocess.run([f"echo \"{evaluation} {sat_str} {script} {instance} {end_systems[0]}_to_{end_systems[1]}\" >> output.txt"], shell=True)
        gc.collect()
    
    except subprocess.TimeoutExpired:
        return

def compare_others_to_ezsmt(folder, script, instance):
    end_systems =["clingcon", "ezsmt"]                                # for ezsmt and clingcon
    try:
        end_sys = end_systems[0]
        command = f"{end_sys} {script} {instance}"                                            # for ezsmt and clingoLP
        print(command)
        with open(f"{end_sys}_output.txt", "w") as file:
            subprocess.run([command], shell=True, stdout=file, stderr=file, timeout=15)
            gc.collect()
        con_sat = check_sat(end_sys)
        if con_sat:
            prepare_debug_file()
        
        end_sys = end_systems[1]
        # command = f"{end_sys} {folder}/encodings/theory.lp {script} {instance}"                     # for ezsmt and clingcon
        command = f"{end_sys} {script} {instance}"                                                  # for ezsmt and clingcon
        
        if con_sat:
            command += " debug.lp"
        print(command)
        with open(f"{end_sys}_output.txt", "w") as file:
            subprocess.run([command], shell=True, stdout=file, stderr=file, timeout=15)
            gc.collect()
        ez_sat = check_sat(end_sys)

        evaluation, sat_str = get_eval([ez_sat, con_sat])
        subprocess.run([f"echo \"{evaluation} {sat_str} {script} {instance} {end_systems[0]}_to_{end_systems[1]}\" >> output.txt"], shell=True)
        gc.collect()
    
    except subprocess.TimeoutExpired:
        return

def main():
    if os.path.exists("output.txt"):
        os.remove("output.txt")

    for folder in glob.glob(f"{BENCHMARK_FOLDER}/*"):
        if not folder.endswith("weighted-sequence"):
            continue
        scripts = [script for script in glob.glob(f"{folder}/encodings/*") if script.endswith((".lp", ".con"))]
        for script in scripts:
            if "theory" in script:
                continue
            for instance in glob.glob(f"{folder}/instances/*"):
                compare_ezsmt_to_others(folder, script, instance)
                compare_others_to_ezsmt(folder, script, instance)


if __name__ == "__main__":
    main()
            
