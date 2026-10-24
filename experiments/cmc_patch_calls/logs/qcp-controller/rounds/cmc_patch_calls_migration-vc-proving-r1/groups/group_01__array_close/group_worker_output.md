# array_close proof delivery

Both CALL and non-CALL recursive return witnesses and their spatial split goals are proved. The paired-array cons helper is unconditional: it preserves the opcode/int64-immediate head cells and reassembles shifted tails without adding program premises. Existing `cm_patch_code_length`, standard full-array unfolding and segment rebasing provide the required bridges.

```json
{"development_calls":5,"development_failed":4,"debug_calls":0,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":1}
```

Repairs: added the official `Lia` import because the library does not inherit the tactic; replaced implicit/default cancellation (which left reordered resources) with explicit resource cancellation in the helper. One development failure used `Show` to inspect this residual goal, and the diagnostic command was removed. No annotation or model edits were necessary. The mandatory controller acceptance remains separate from the optional checks reported here.
