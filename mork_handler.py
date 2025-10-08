import os
import subprocess
import time
import uuid
from typing import List, Tuple
from helpers.sexpr_converter import convert_sexpr

from petta import PeTTa                                                                                                                                                                

class MorkHandler:                                                          
    def __init__(self):
        self.handler = PeTTa()

        self.handler.load_metta_file("compile.metta")

        uid = uuid.uuid4().hex
        self.data_file = f"data_{uid}.mm2"
        self.out_file = f"out_{uid}.mm2"
        with open(self.data_file, "w") as f:
            f.write("")

    def __del__(self):
        if os.path.exists(self.data_file):
            os.remove(self.data_file)
        if os.path.exists(self.out_file):
            os.remove(self.out_file)

    def add_atom(self, atom: str, log:bool=False, timeout: float = 240) -> str:
        atoms = self.handler.process_metta_string(f"!(mm2compile {atom})")
        with open(self.data_file, "a") as f:
            for a in atoms:
                f.write(a)
                f.write("\n")
        return atoms

    def query(self, atom: str, log: bool = False, timeout: float = 300.0) -> List[str]:
        """Query the knowledge base and return results
        
        Args:
            atom: The atom to query
            log: Whether to log the output
            timeout: Maximum time in seconds to wait for completion
            
        Returns:
            Tuple of (results_list, proven_boolean)
        """
        atoms = self.handler.process_metta_string(f"!(mm2compileQuery {atom})")
        with open(self.data_file, "a") as f:
            for a in atoms:
                f.write(a)
                f.write("\n")

        p_arg = convert_sexpr(atoms[0], True).replace("goal", "ev")
        t_arg = convert_sexpr(atoms[0], False).replace("goal", "ev")
        cmd = [
            "mork", "run", "--steps", "300",
            "mm2/chainer.mm2", "mm2/mathrels.mm2", self.data_file,
            "-o", self.out_file,
            "-p", p_arg,
            "-t", t_arg
        ]
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            raise RuntimeError(f"mork run failed with return code {result.returncode}: {result.stderr}")

        with open(self.out_file, "r") as f:
            results = f.read().splitlines()
        return results

if __name__ == '__main__':
    handler = MorkHandler()

    print("Test")

    print(handler.add_atom("(: fact1 A (STV 1.0 1.0))"))
    print(handler.add_atom("(: rule1 (Implication A C) (STV 1.0 1.0))"))

    print(handler.query("(: $prf C $tv)"))
