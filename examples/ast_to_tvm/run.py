"""Run: python3 examples/ast_to_tvm/run.py

Builds the 31 original migrated C units directly, with their QCP comments
intact. The tiny simulator below exercises only the instructions in this
example; it is an explanatory check, not the project's verified TVM model.
"""
from pathlib import Path
import subprocess
import tempfile

here = Path(__file__).resolve().parent
root = here.parent.parent
sources = sorted((root / "experiments").glob("cmc_*/target/*_migration.c"))
assert len(sources) == 31, f"Recheck source list: {len(sources)} units"
with tempfile.TemporaryDirectory(prefix="cmc-ast-demo-") as build:
    exe = Path(build) / "demo"
    subprocess.run(["clang", "-std=c11", "-O0", "-g",
                    "-fsanitize=undefined",
                    "-I", str(root / "experiments/cmc_layout/target"),
                    *map(str, sources), str(here / "demo.c"),
                    "-o", str(exe)], check=True)
    result = subprocess.run([str(exe)], check=True, text=True,
                            capture_output=True, timeout=20).stdout
(here / "output.txt").write_text(result)
print(result)

code = []
for line in result.splitlines():
    cols = line.split()
    if len(cols) == 4 and cols[0].isdigit():
        code.append((cols[1], int(cols[3])))
memory = bytearray(1048576)
data_line = next(line for line in result.splitlines() if line.startswith("data:"))
data = bytes.fromhex(data_line[5:])
memory[8:8 + len(data)] = data
stack, calls, trace = [], [], []
pc = 0
def load(address):
    assert 0 <= address <= len(memory) - 8
    return int.from_bytes(memory[address:address+8], "little", signed=True)
def store(address, value):
    assert 0 <= address <= len(memory) - 8
    memory[address:address+8] = value.to_bytes(8, "little", signed=True)
for step in range(1000):
    op, imm = code[pc]
    old_pc, next_pc = pc, pc + 1
    if op == "PUSH": stack.append(imm)
    elif op == "POP": stack.pop()
    elif op == "DUP": stack.append(stack[-1])
    elif op == "SWAP": stack[-2], stack[-1] = stack[-1], stack[-2]
    elif op == "LOAD": stack.append(load(stack.pop()))
    elif op == "STORE":
        address = stack.pop()
        store(address, stack.pop())
    elif op in ("ADD", "SUB", "MOD"):
        b, a = stack.pop(), stack.pop()
        if op == "ADD": value = a+b
        elif op == "SUB": value = a-b
        else:
            assert b != 0
            q = (abs(a)//abs(b)) * (-1 if (a<0) != (b<0) else 1)
            value = a-q*b
        stack.append(((value + 2**63) % 2**64) - 2**63)
    elif op == "CALL":
        calls.append(pc+1)
        next_pc = imm
    elif op == "RET": next_pc = calls.pop()
    elif op == "HALT":
        status = stack.pop()
        trace.append(f"{step:02d} pc={old_pc:02d} HALT status={status}")
        assert status == 5 and not calls
        break
    else: raise ValueError(op)
    trace.append(f"{step:02d} pc={old_pc:02d} {op} {imm}: stack={stack}, fp={load(8)}, next={next_pc}")
    pc = next_pc
else: raise AssertionError("Step limit exceeded")
trace.append("input=[] output=[] status=5")
(here / "trace.txt").write_text("\n".join(trace) + "\n")
print(trace[-1])
