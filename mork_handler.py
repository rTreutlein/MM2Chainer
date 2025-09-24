import random
import string
import os
import subprocess
import time
import selectors
import re
import time
import sys
from order import parse_sexpr, print_sexpr, build_structure
from typing import List, Tuple
from sexpr_converter import convert_sexpr

from mettalog_handler import MettalogHandler

class MorkHandler:                                                          
    def __init__(self):
        self.handler = MettalogHandler()
        with open("data.mm2", "w") as f:
            f.write("")

    def add_atom(self, atom: str, log:bool=False, timeout: float = 240) -> str:
        atoms = self.handler.run(f"!(mm2compile {atom})")
        with open("data.mm2", "a") as f:
            for a in atoms:
                f.write(a)
                f.write("\n")

    def query(self, atom: str, log: bool = False, timeout: float = 300.0) -> List[str]:
        """Query the knowledge base and return results
        
        Args:
            atom: The atom to query
            log: Whether to log the output
            timeout: Maximum time in seconds to wait for completion
            
        Returns:
            Tuple of (results_list, proven_boolean)
        """
        atoms = self.handler.run(f"!(mm2compileQuery {atom})")
        print(atoms)
        with open(f"data.mm2", "a") as f:
            for a in atoms:
                f.write(a)
                f.write("\n")

        os.system(f"mork run --steps 150 chainer.mm2 mathrels.mm2 data.mm2 -o out.mm2 -p \"{convert_sexpr(atoms[0],True).replace("goal","ev")}\" -t \"{convert_sexpr(atoms[0],False).replace("goal","ev")}\"")

        with open("out.mm2", "r") as f:
            results = f.read().splitlines()
        return results

if __name__ == '__main__':
    handler = MorkHandler()

    handler.add_atom("(: fact1 A (STV 1.0 1.0))")
    handler.add_atom("(: rule1 (Implication (And A B) C) (STV 1.0 1.0))")

    print(handler.query(("(: $prf (Implication B C) $tv)")))
