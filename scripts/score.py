#!/usr/bin/env python3
import os
from pathlib import Path

def count_lean_files(dirpath: str) -> int:
    p = Path(dirpath)
    if not p.exists():
        return 0
    return sum(1 for f in p.rglob('*.lean') if f.is_file())

sol = count_lean_files('Solutions')
canon = count_lean_files('MoltResearch')
tasks = count_lean_files('Tasks')
conj = count_lean_files('Conjectures')

print(f"solutions_lean_files={sol}")
print(f"canonical_lean_files={canon}")
print(f"tasks_lean_files={tasks}")
print(f"conjecture_lean_files={conj}")
