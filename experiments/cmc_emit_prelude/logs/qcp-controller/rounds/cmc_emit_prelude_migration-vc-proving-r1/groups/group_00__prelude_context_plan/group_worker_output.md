# Proof effort

```json
{"development_calls":5,"development_failed":4,"debug_calls":4,"debug_failed":1,"exact_calls":1,"exact_failed":0,"new_helpers":0}
```

Completed all three assigned top-level witnesses and all seven assigned split goals. No helper or library changes were needed. The program-context representation is opened and reclosed around the read, opcode equalities reduce through the required explicit preprocessor closer, and the result list uses standard append associativity followed by spatial cancellation.

Actual repairs: removed redundant Intros_p after Intros had already extracted the nonzero fact; repeated spatial cancellation to consume each identical field/list resource; removed redundant follow-on pure proof commands after LLM_pre_process had already closed opcode goals; put the spatial Goal_apply first to match aggressive_pre_process branch order. One debug call initially lacked the sac scope imports; its script was repaired using the copied manual's imports. The final development and exact group checks passed.
