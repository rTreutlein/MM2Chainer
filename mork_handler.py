import os
import subprocess
import time
import uuid
import threading
from typing import List, Tuple
from helpers.sexpr_converter import convert_sexpr

from petta import PeTTa                                                                                                                                                                
import logging

logging.basicConfig(
    format="%(asctime)s [%(levelname)s] %(message)s",
    level=logging.INFO
)
logger = logging.getLogger(__name__)

LOADEDLIB = False
LOADED_LOCK = threading.Lock()

class MorkHandler:                                                          
    def __init__(self):
        global LOADEDLIB
        self.handler = PeTTa()
        
        self.kb = "kb" + uuid.uuid4().hex

        if not LOADEDLIB:
            with LOADED_LOCK:
                if not LOADEDLIB:
                    src_path = os.path.join(os.path.dirname(__file__),"metta/compile.metta")
                    print(src_path)
                    self.handler.load_metta_file(src_path)
                    LOADEDLIB = True

        self.data_file = f"data_{self.kb}.mm2"
        self.out_file = f"out_{self.kb}.mm2"
        with open(self.data_file, "w") as f:
            f.write("")

    def __del__(self):
        if os.path.exists(self.data_file):
            os.remove(self.data_file)
        if os.path.exists(self.out_file):
            os.remove(self.out_file)

    def add_atom(self, atom: str, log:bool=False, timeout: float = 240) -> str:
        atoms = self.handler.process_metta_string(f"!(mm2compile {self.kb} {atom})")
        if len(atoms) == 0:
            if log:
                print(f"No atoms found for {atom}")
            return
        with open(self.data_file, "a") as f:
            for a in atoms:
                if log:
                    print(a)
                    print("\n")
                f.write(a)
                f.write("\n")
        return atoms

    def query(self, atom: str, log: bool = False, timeout: int = 3) -> List[str]:
        """Query the knowledge base and return results
        
        Args:
            atom: The atom to query
            log: Whether to log the output
            timeout: Maximum time in seconds to wait for completion
            
        Returns:
            Tuple of (results_list, proven_boolean)
        """
        atoms = self.handler.process_metta_string(f"!(mm2compileQuery {self.kb} {atom})")
        with open(self.data_file, "a") as f:
            for a in atoms:
                if log:
                    print(a)
                    print("\n")
                f.write(a)
                f.write("\n")
            f.write(atoms[0].replace("goal", "pgoal"))

        p_arg = convert_sexpr(atoms[0], True).replace("goal", "ev")
        t_arg = convert_sexpr(atoms[0], False).replace("goal", "ev")
        chainer_file = os.path.join(os.path.dirname(__file__), "mm2" , "chainer.mm2")
        mathrels_file = os.path.join(os.path.dirname(__file__), "mm2" , "mathrels.mm2")
        cmd = [
            "mork", "run",
            #"--steps", "3000",
            chainer_file, mathrels_file, self.data_file,
            "-o", self.out_file,
            "-p", p_arg,
            "-t", t_arg,
            "--timeout", str(int(timeout))
        ]
        if log:
            print(atoms)
            print(cmd)
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            raise RuntimeError(f"mork run failed with return code {result.returncode}: {result.stderr}")

        with open(self.out_file, "r") as f:
            results = f.read().splitlines()
        return results

if __name__ == '__main__':
    handler = MorkHandler()

    print("Test")
    print(handler.add_atom("(: a A (STV 1.0 1.0))"))
    print(handler.add_atom("(: b_a (Implication B A) (STV 1.0 1.0))"))

    print(handler.query("(: $prf A $tv)"))
