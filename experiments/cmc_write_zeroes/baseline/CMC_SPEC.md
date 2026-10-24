# Verified CMC compiler specification

## 1. Purpose

CMC is a verified compiler from a typed, name-resolved Tower C− abstract syntax
tree to a resolved Tower Virtual Machine (TVM) object. Its public entry point is:

```c
int cmc_compile(struct cm_program *program, struct cm_output *output);
```

This document specifies the boundary proved for that function. It also records
the TVM semantics used as the compiler's target and the relationship of the
separately verified Tower assembler (TASM) resolver. CMC does **not** compile
through TASM:

```text
canonical cm_program ── verified CMC ──> resolved tvm_object ──> TVM semantics

post-parse TASM items ── separate verified resolver ──────────┘
```

The C ABI declarations in `cmc.h` and `cmc_abi.h` are authoritative for
concrete field names, tags, and integer encodings. The formal predicates,
contracts, and theorem statements are authoritative for the verified boundary;
this document describes their interpretation and the completed audit.

## 2. Verified boundary

### 2.1 Input boundary

The compiler receives a caller-owned `struct cm_program` graph that already
represents a `cm_wf_program`:

- the graph is finite, acyclic, unshared, and canonical;
- all types, descriptor IDs, bindings, members, calls, and string references
  are resolved and in range;
- every expression carries its proved result type;
- every function body is present and the entry is argument-free `int main()`;
- source object sizes, target addresses, code lengths, frame sizes, and stack
  bounds satisfy the compiler's admissibility conditions.

Here `cm_wf_program p` is exactly `cm_codegen_admissible p`, not merely
`cm_typed_program p`. Besides source typing, it assumes:

- nonnegative model code length at most `2,147,483,647`;
- nonnegative model data length at most `1,048,568` bytes;
- nonnegative model operand-stack bound at most `65,536`;
- `cm_codegen_counts_representable p`, covering intermediate function/statement/
  expression counts and function PCs;
- `cm_codegen_fields_representable p`, which requires `tvm_code_shape` and
  `tvm_targets_valid` for the **model-generated code**, `tvm_patches_valid` for
  its model data patches, and `tvm_target_valid` for entry PC zero.

In particular, model-generated target validity is an explicit admissibility
premise. The current theorem does not derive all these target-validity
conditions from source typing alone.

This is a precondition, not a validation service. Behavior for a malformed,
untyped, aliased, cyclic, or otherwise noncanonical graph is outside the
verified contract.

### 2.2 Output boundary

On success, the output representation contains the exact model-generated
opcode, immediate, and data prefixes for one resolved TVM object. Labels,
symbolic references, textual assembly, and backpatch records do not cross this
boundary. On insufficient capacity, the contract reports both exact required
lengths and entry `-1`; it makes no claim about output-array contents.

Both outcomes return `cm_program_rep program p` for the same model program
`p`. This preserves the represented AST, not a byte-for-byte snapshot or the
identity of every pointer in the concrete graph.

### 2.3 Semantic guarantee

The principal theorem is terminating forward preservation:

```text
!p input output status.
  cm_wf_program p /\ cm_source_terminates p input output status
  ==> tvm_terminates (cm_compile_model p) input output status
```

Thus, whenever a well-formed source program has a successful terminating
execution with input bytes, ordered output bytes, and process status, the
compiled TVM object has a terminating normal execution with exactly the same
observations. A separate corollary proves that the compiled object cannot reach
a TVM runtime error under the same premises.

`cm_source_terminates` includes valid input bytes, a byte-valued exit status,
and an execution ending in successful source control with the stated output.
"Successful" excludes source errors; it does not require exit status zero.

The successful `cmc_compile` postcondition, `cm_output_ok`, directly includes
the composed semantic guarantee as a universally quantified pure fact:

```text
!obj input trace status.
  cm_source_terminates p input trace status /\
  cm_output_decodes 0
    (cm_rep_ops (cm_model_code p))
    (cm_rep_imms (cm_model_code p))
    (cm_model_data_bytes p) obj
  ==> tvm_terminates obj input trace status
```

These are exactly the opcode, immediate, and data lists specified by the
buffer predicates in that same postcondition. The compiler establishes this
fact using the concrete decoding bridge and the model preservation theorem;
callers need not compose those theorems themselves.
The formal `cm_output_ok` definition writes each boolean predicate application
with `<=> true` inside the quantified fact so it can be unfolded and consumed
by C* callers. Those wrappers do not add assumptions or change the implication.

Successful source termination remains a premise of the implication, not a
precondition for calling the compiler. The capacity-failure postcondition is
unchanged and carries no execution guarantee.

### 2.4 Claims deliberately not made

The proof does not cover:

- lexing, parsing, escapes, source-file syntax, name resolution, or type
  checking used to construct `cm_program`;
- textual TASM or TVM parsing, serialization, command-line tools, files, or OS
  I/O adapters;
- source executions that end in a source error;
- divergence preservation, termination reflection, behavioral equivalence, or
  a converse from target executions to source executions;
- a separate total-correctness proof that the C compiler call itself terminates;
- byte-for-byte input-heap preservation, preservation of all internal or output
  pointer identities, or unchanged output-array cells on capacity failure;
- optimization, separate compilation, dynamic linking, or self-modifying code;
- floating point, threads, variadic functions, indirect calls, or function
  pointers.

## 3. Public compiler API

### 3.1 Ownership and representation

The caller owns the program graph, `struct cm_output`, and all three output
arrays. The owned footprints are pairwise disjoint and the output arrays are
writable. The precondition is:

```text
cm_program_rep program p **
cm_output_pre output code_capacity data_capacity
```

Capacities are nonnegative. Positive `code_capacity` requires non-null `ops`
and `imms` buffers of that capacity; positive `data_capacity` requires a
non-null data buffer. A zero capacity owns no corresponding array cells and
does **not** require its pointer to be null.

Array contents are unspecified before the call. The output structure's fields
must hold typed values: its old lengths and entry are arbitrary, not
`undef_data_at` fields. The postcondition is:

```text
(fact(__return == 0) **
 cm_program_rep program p **
 cm_output_ok output code_capacity data_capacity p)
||
(fact(__return == 1) **
 cm_program_rep program p **
 cm_output_capacity output code_capacity data_capacity p)
```

The only return codes are:

- `CMC_OK == 0`: both capacities suffice. `code_length` and `data_length` are
  exact, `entry == 0`, every `ops[i]`/`imms[i]` pair decodes to the modeled
  instruction, and every `data[i]` is the modeled byte for address `8 + i`.
  The success predicate also carries the semantic guarantee in §2.3. Unused
  array suffix contents are unspecified.
- `CMC_CAPACITY == 1`: at least one capacity is insufficient. Both required
  lengths are exact, `entry == -1`, and the capacity values are preserved.
  The array footprints are returned, but their contents are unspecified.

Both branches retain the supplied capacity values and a representation of the
same model program. The output predicates existentially bind their buffer
pointers afresh; they do not relate those pointers to their pre-call values.
Likewise, the program predicate does not promise identity of all internal
pointers.

The implementation computes both lengths and checks capacities before
constructing an output cursor or emitting bytes. That control-flow property is
not a relational "buffers untouched" guarantee in `cm_output_capacity`.
The verified C contract is a partial-correctness contract: on return under its
precondition, no other return value is possible.

For C* verification, define `CSTAR_VERIFY`, include `cmc.h`, and
`#require "cmc.c"`. The public header exposes the same compiler contract as the
definition, including the strengthened `cm_output_ok` success predicate.

### 3.2 Type and tag encodings

A source type is encoded as:

```text
pointer_depth * 1024 + base
```

where base `0` is `int`, base `1` is `char`, and base `2 + struct_id` names a
structure. `CMC_TYPE_INT`, `CMC_TYPE_CHAR`, `CMC_TYPE_STRUCT(id)`, and
`CMC_TYPE_POINTER(ty)` construct these values.

A slot or member with `count == 0` is scalar; `count > 0` is a fixed array.
Negative counts are invalid.

Expression tags, in order from zero, are:

```text
CONST STRING VAR ASSIGN BINARY UNARY INDEX MEMBER CALL SIZEOF
GETC PUTC PUTI EXIT
```

Statement tags, in order from zero, are:

```text
SKIP EXPR DECL INIT SEQ BLOCK IF WHILE BREAK CONTINUE RETURN
```

Binding tags are `GLOBAL`, `LOCAL`, and `PARAM`. Binary operation tags are
`OR`, `AND`, `EQ`, `NE`, `LT`, `LE`, `GT`, `GE`, `ADD`, `SUB`, `MUL`, `DIV`,
and `MOD`; unary tags are `NEG`, `NOT`, `DEREF`, and `ADDR`.

Unused fields are zero or null. The canonical payload interpretation is:

- `CONST.value` is the literal; `STRING.value` is a string ID;
- `VAR.op` is the binding scope and `VAR.value` is the dense binding ID;
- assignment, binary, and index expressions use `a` and `b`;
- unary expressions use `op` and `a`;
- member access uses `a` and member ID `value`;
- calls use function ID `value` and the `args` list;
- `SIZEOF.value` is an encoded type;
- `PUTC`, `PUTI`, and `EXIT` use `a`;
- declarations use local `slot`; `INIT` also uses `expr`;
- `EXPR` and `RETURN` use `expr`; `SEQ` uses `a` and `b`; `BLOCK` uses `a`;
  `IF` uses `expr`, `a`, and `b`; `WHILE` uses `expr` and `a`.

## 4. Verified Tower C− source semantics

### 4.1 Values and arithmetic

`int` is a signed 64-bit value, `char` is an unsigned byte in `0..255`, and a
pointer occupies one 8-byte cell. For mathematical integer `z`:

```text
wrap64(z) = ((z + 2^63) mod 2^64) - 2^63
u8(z)     = z mod 256
status(z) = u8(z)
```

Both modulo expressions above denote their unique nonnegative residue.
Addition, subtraction, multiplication, and unary negation apply `wrap64`.
Comparisons and logical operators produce integer `0` or `1`. `&&` and `||`
short-circuit.

Division truncates toward zero. For nonzero `b`, let

```text
q = sign(a * b) * floor(abs(a) / abs(b))
```

Then division is `wrap64(q)` and remainder is `wrap64(a - q * b)`.
`INT64_MIN / -1` therefore wraps to `INT64_MIN`, with remainder zero. Division
or remainder by zero is a source error.

A `char` promotes to `int` by zero extension. Assignment, initialization,
argument passing, and return share one conversion relation:

- identical scalar or pointer types preserve the value;
- `int` accepts `int` and zero-extended `char`;
- `char` accepts `int` or `char` through `u8`;
- a pointer accepts the same pointer type;
- a pointer accepts literal integer zero as null;
- `char *` and any object-pointer type may convert in either direction through
  the byte-pointer bridge.

No other implicit conversion is valid.

### 4.2 Objects and layout

Source types are `int`, `char`, named structures, and recursively nested
pointers. Direct structure values are prohibited: structures occur in member
descriptions and beneath pointers only.

```text
sizeof(int)     = 8
sizeof(char)    = 1
sizeof(pointer) = 8
```

A positive fixed array has size `count * sizeof(element)`. Structure members
and array elements are laid out consecutively in declaration order with no
padding. Eight-byte values may be unaligned.

One-dimensional arrays may contain integers, characters, or pointers.
Structure members may be scalars or one-dimensional fixed arrays of those
types. Arrays cannot be initialized as a whole. Scalar global initializers are
signed integer literals converted to the declared type; only literal zero may
initialize a pointer.

### 4.3 Pointer provenance and memory safety

A non-null source pointer carries a storage generation, a live half-open
provenance region, a byte offset from the generation's base, and a typed view.
Only `base + offset` is encoded numerically in TVM memory. Null encodes as zero;
provenance metadata is semantic and is not emitted as target bytes.

Scalar declarations create one-object regions. Array decay retains the whole
array region. Taking the address of a scalar member narrows the region to that
member; taking the address of an array member retains the complete member-array
region. Every parameter activation and every execution of a local declaration
gets a fresh generation. Reusing a frame address does not revive a pointer to a
dead generation.

For pointee size `s`, `p+n`, `n+p`, and `p-n` adjust the byte offset by `n*s`.
The result may be inside the live region or exactly one-past its upper bound;
one-past pointers cannot be dereferenced. Pointer subtraction requires the
same live generation, region, and typed view, with a difference divisible by
`s`. Relational comparison requires compatible views in the same live region.
Equality compares numerical addresses for compatible pointer types, including
null.

The `char *` bridge changes only the typed view, retaining generation, region,
and offset. It permits objects to be carved from a global byte array without a
cast syntax.

The source memory model tracks validity, initialization, lifetime, write
permission, and pointer-provenance tags per byte. A byte write overlapping a
stored pointer clears its tag. An all-zero pointer cell loads as null; any other
untagged nonzero pointer load is a source error. Invalid, dead,
out-of-bounds, write-protected, or uninitialized access is likewise a source
error.

Addresses satisfy `0 <= address < 1,048,576`. A byte access touches one valid
address. An 8-byte little-endian access may start unaligned but all eight bytes
must be valid.

### 4.4 Control and observations

Expressions include constants, strings, variables, assignment, unary and
binary operations, indexing, `->` member access, calls, `sizeof`, and the four
intrinsics. Statements include declarations, sequencing, blocks, conditionals,
loops, `break`, `continue`, and return. Functions may recurse.

Evaluation order is fixed:

- assignment evaluates its destination before its source;
- non-short-circuit binary operators evaluate left then right;
- indexing evaluates the base before the index;
- initializers and call arguments evaluate left to right;
- `&&` and `||` evaluate the right operand only when required.

Falling off a function returns integer zero converted to its return type. A
normal `main` return and `cm_exit` both produce `status(value)`.

The intrinsic observations are:

- `cm_getc()` consumes and returns the next input byte, or `-1` at EOF;
- `cm_putc(c)` appends `u8(c)` to output and returns converted integer `c`;
- `cm_puti(n)` appends the signed-decimal ASCII representation of `n` and
  returns `n`;
- `cm_exit(c)` terminates immediately with `status(c)`.

Output remains ordered. Exit and source errors propagate immediately through
enclosing expressions, statements, loops, and calls.

## 5. Verified layout and code generation

### 5.1 Static and frame layout

Address `8` is the compiler-managed 8-byte frame-pointer cell. Static objects
begin at address `16`: globals in descriptor order, followed by read-only
NUL-terminated strings in descriptor order. Source objects are not padded.

A call from frame pointer `old_fp` uses `new_fp = old_fp - frame_size`. Frame
offset zero stores the caller frame pointer, followed by parameters, locals,
and compiler-only 8-byte spill slots in descriptor order. Slots are not reused
within a frame. Calls are admitted only when their downward frame range is
valid and fewer than 65,536 source call frames are active.

Spill demand is structural. If `ltemps(e)` and `rtemps(e)` are the slots needed
to form an lvalue or value:

- variables need zero;
- dereference/member lvalues use the operand's value demand;
- indexed lvalues need `max(rtemps(base), 1 + rtemps(index))`;
- constants, strings, variables, `sizeof`, and `GETC` need zero value spills;
- address-of uses its operand's lvalue demand;
- unary values and output/exit intrinsics use their operand's value demand;
- member and index values use the whole expression's lvalue demand;
- assignment needs `max(ltemps(destination), 1 + rtemps(source))`;
- ordinary binary expressions need
  `max(rtemps(left), 1 + rtemps(right))`;
- `AND` and `OR` need `max(rtemps(left), rtemps(right))`;
- an `n`-argument call needs `n + max(rtemps(argument_i))`, with empty maximum
  zero.

Statement demand is the maximum of its expressions and children. Each function
reserves exactly its body's demand.

### 5.2 Resolved output

CMC emits instructions directly with resolved numeric jump and call targets.
The object entry is zero. Its prelude initializes the frame pointer to
`1,048,576`, calls `main`, normalizes the returned status into `0..255`, and
halts. Function code allocates and restores frames, stages arguments left to
right, preserves earlier operands in frame spills across nested calls, and
includes a return-zero fallthrough epilogue. Every expression and statement
fragment is operand-stack normal.

The exact structural operand-stack bound is:

```text
3 + max_function_arity(program)
```

using zero for an empty maximum. It must not exceed 65,536. Admissibility also
requires the code/data length bounds, representable counts and function PCs,
and model-generated instruction, target, patch, and entry validity listed in
§2.1. These are premises of preservation, not runtime validation performed by
`cmc_compile`.

The data array represents consecutive memory bytes starting at address `8` and
contains the frame-pointer cell image, global initializers or zero-fill, and
string bytes.

## 6. TVM target semantics used by the proof

### 6.1 Object and machine state

The formal target is an in-memory `tvm_object`, not a textual `.tvo` file. It
contains an entry instruction index, a resolved instruction sequence, and a
list of `(address, byte)` data patches.

TVM state comprises:

- an operand stack of at most 65,536 signed 64-bit values;
- a call stack of at most 65,536 return instruction indices;
- exactly 1,048,576 byte-addressable memory bytes, initially zero before data
  patches are applied;
- the current PC, input-byte list, and ordered output-byte list.

Execution begins at the object's entry PC after object validation and patch
application. Unless stated otherwise, an instruction advances PC by one.
Binary operations pop `b`, then `a`, and compute `a OP b`.

### 6.2 Instructions

Opcode values are stable and shared with `CMC_OP_*`:

| Code | Instruction | Effect |
|---:|---|---|
| 0 | `PUSH n` | Push wrapped signed-64 immediate `n`. |
| 1 | `POP` | Discard the top operand. |
| 2 | `DUP` | Duplicate the top operand. |
| 3 | `SWAP` | Swap the top two operands. |
| 4 | `LOAD` | Pop an address; load an unaligned 8-byte little-endian word. |
| 5 | `STORE` | Pop an address, then a value; store its 8-byte little-endian representation. |
| 6 | `LOADB` | Pop an address; push its byte, zero-extended. |
| 7 | `STOREB` | Pop an address, then a value; store its low eight bits. |
| 8–10 | `ADD`, `SUB`, `MUL` | Wrapped signed-64 arithmetic. |
| 11–12 | `DIV`, `MOD` | Truncation-toward-zero quotient or remainder; zero divisor is an error. |
| 13–18 | `EQ`, `NE`, `LT`, `LE`, `GT`, `GE` | Signed comparison; push `0` or `1`. |
| 19 | `JMP t` | Set PC to `t`. |
| 20 | `JZ t` | Pop a value; jump to `t` exactly when it is zero. |
| 21 | `JNZ t` | Pop a value; jump to `t` exactly when it is nonzero. |
| 22 | `CALL t` | Push `PC + 1` on the call stack and jump to `t`. |
| 23 | `RET` | Pop the call stack into PC. |
| 24 | `GETC` | Consume and push one input byte, or push `-1` at EOF. |
| 25 | `PUTC` | Pop a value and append its low byte to output. |
| 26 | `PUTI` | Pop a value and append its signed-decimal ASCII representation. |
| 27 | `HALT` | Pop and return a status in `0..255`; any other value is an error. |

Only `PUSH`, `JMP`, `JZ`, `JNZ`, and `CALL` carry a nonzero immediate in a
canonical CMC object.

### 6.3 Target errors

Object loading rejects malformed instruction shapes, patches, entry points, or
control-flow targets. Runtime errors are:

- operand-stack underflow or overflow;
- call-stack underflow or overflow;
- byte or word access touching an address outside memory;
- division or remainder by zero;
- a jump or call target outside the code sequence;
- PC falling past the code sequence without `HALT`;
- `HALT` with a value outside `0..255`.

The formal model distinguishes normal termination, runtime error, and malformed
object outcomes. Its I/O is list-based; any textual object loader, buffering,
stderr wording, and process exit convention are outside the CMC theorem.

## 7. TASM relationship

TASM is an adjacent verified resolver, not a phase of CMC. Its formal input is
already parsed into a list of structured `tasm_item` values. Items represent
code/data section changes, an entry reference, labels, resolved opcodes with
immediate/code-reference/data-reference operands, word and byte data,
NUL-terminated byte strings, and zero-filled space.

Resolution starts in the code section with code PC zero and data address eight.
It builds one label environment, resolves code labels to instruction indices
and data labels to addresses, emits a resolved `tvm_object`, and selects a
deterministic error result when the structured input is invalid.

The separately proved properties are:

```text
tasm_resolve items = result1 /\ tasm_resolve items = result2
==> result1 = result2
```

and:

```text
tasm_items_wf items /\ tasm_resolve items = TasmOk obj
==> tasm_denotes items obj
```

A further bridge proves that a denoted object is TVM-well-formed when its data
fits. These theorems begin **after parsing**. Identifier spelling, comments,
decimal and character syntax, escape processing, `.tasm`/`.tvo` text formats,
and assembler or VM command-line behavior are not verified here.

CMC bypasses this resolver and emits numeric targets directly. The concrete
emitter is verified to realize the model code exactly; model-generated target
validity is supplied by the admissibility premise in §2.1. No CMC correctness
claim depends on `tasm_resolve`.

## 8. Proof surface and trust accounting

The load-bearing verification units are:

| File | Role |
|---|---|
| `tower_base.c` | Shared signed-64, byte, status, address, and memory definitions. |
| `cmc_lang.c` | Tower C− syntax, typing, provenance memory, and source execution. |
| `tvm_model.c` | Resolved TVM objects, loader, transitions, termination, and errors. |
| `tasm_model.c` | Independent post-parse TASM denotation and resolver proofs. |
| `cmc_codegen.c` | Exact sizing, layout, emission, and stack-bound models. |
| `cmc_correct.c` | Source-to-TVM preservation and no-runtime-error theorems. |
| `cmc_rep.c` | Concrete heap graph, exact output-array representation, and the semantic success predicate. |
| `cmc_concrete_*.c` | Concrete sizing, layout, emission, patching, and supporting proofs. |
| `cmc.h` | Public C* compiler contract, with the native C declaration retained outside verification builds. |
| `cmc.c` | Verified compiler body, concrete success bridge, and construction of the semantic success postcondition. |

The source semantics uses an impredicative least big-step relation over
mutually recursive expression-lvalue, expression-rvalue, statement, and call
tasks. TVM execution defines loading and all 28 instruction transitions. Code
generation defines exact pure sizing and emission functions before connecting
them to the concrete buffer implementation.

### 8.1 Verification boundary and trust

The model preservation theorem, the decoding bridge, and the C function
contract remain separate proof components. The compiler's success proof now
composes them when establishing `cm_output_ok`, so a caller receives the
semantic implication from the C contract rather than having to apply the
bridge independently.

Importing a module with `#require` runs its proof initializers and exposes its
contracts; it does **not** independently discharge the ordinary C bodies in
that module. A clean `cmc.c` endpoint alone therefore does not certify all
helper implementations. Each ordinary helper unit must also be checked at its
own final file-scope endpoint.

The proof modules contain closedness/non-null checks for published
load-bearing theorems and axiom-count guards. The audit's acceptance condition
for every endpoint was `flag: true` with all three lists empty:

```text
verification_conditions: []
axioms: []
strategies: []
```

This records discharged obligations without additional recorded axioms or
strategies; it is not a claim that the underlying logic has no axioms. The
trusted boundary includes HOL Light's kernel and foundational theory, C*'s
translation and verification machinery, and the correspondence between the
formal models and the intended languages. Native compilation, external object
loaders, and an independently implemented VM are not proved correct by this
audit.

### 8.2 Audit, repairs, and completed revalidation

The initial independent helper audit covered 30 C units containing 131
ordinary C definitions. Twenty-five units verified; five required repairs:

| Unit | Repaired issue |
|---|---|
| `cmc_concrete_counts.c` | Missing declaration and proof-module dependency for the function-prefix theorem. |
| `cmc_concrete_function_pc_total.c` | The same missing function-prefix theorem dependency. |
| `cmc_concrete_emit_binary_finish.c` | An unmatched parenthesis in a proof contract. |
| `cmc_concrete_emit_code.c` | Missing stack-local-syntax proof dependency. |
| `cmc_concrete_emit_stmt.c` | Seventeen residual VCs: PC arithmetic and fragment bounds, temporary-slot bounds, recursive-call preconditions, and sequence-result/postcondition bookkeeping. |

The statement repair also updated `cmc_concrete_emit_stmt_proof.c`, including
the integer-conversion facts needed at recursive calls. These repairs did not
change runtime C behavior or weaken admissibility or source-termination
premises.

The subsequent contract update strengthened `cm_output_ok` with the quantified
semantic implication, established it from the existing bridge in `cmc.c`, and
exposed the contract through `cmc.h`. The representation layer now depends on
`cmc_abi.h` directly, avoiding a dependency cycle through the public compiler
header. The compiler precondition and capacity-failure branch are unchanged.

Final revalidation against the strengthened contract passed at 34 endpoints:

- all 30 ordinary helper units, covering all 131 audited C definitions;
- the representation module `cmc_rep.c` and the changed statement proof helper;
- the public compiler implementation, at `cmc.c:671`;
- a temporary caller that invoked `cmc_compile`, unfolded the successful
  `cm_output_ok`, and derived `tvm_terminates` for supplied source observations
  and a decoded object without invoking the preservation bridge.

Every endpoint met the empty-list criterion in §8.1, and the recorded source
hashes matched the verified sources. The public header also passed a native
C11 syntax check. Temporary probe sources and verification drivers were
removed; the successful caller's source was retained in its local evidence
record.

Generated, local-only evidence is stored under `_verif/`: `helper-audit/`
records the original failures, `helper-repair/` records the repairs, and
`semantic-contract/` records the final strengthened-contract checks.
`semantic-contract/summary.json`, `manifest.json`, `compiler.json`, and
`caller.json` contain the final coverage, source hashes, and compiler/caller
results. These artifacts are not part of the versioned specification; future
code changes require fresh verification rather than reliance on this audit
snapshot.
