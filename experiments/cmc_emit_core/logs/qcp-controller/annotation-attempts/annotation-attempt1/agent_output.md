# Annotation design

All nine source runtime bodies retained. Emitter models use builtin int/int64 segment ownership; segments are the same source prefix plus shifted undefined suffix. No new scalar, fid-validity or program-wf assumptions. The same lookup policy as the verified counts/function-PC model is retained.

The exact layout cmc_temp_offset helper contract is redeclared; its implementation remains the verified dependency. The globals library is imported solely to reuse its proved scalar representation-size bridge. No prior manual/auto artifacts imported.

References: verified layout/counts/function_pc_total C and pure models determine reused interfaces; QCP sum and array guide inform basic annotation syntax. Negative algorithm-mirror example is rejected: source fragments are caller-observable instruction lists, not an interpreter of these C functions.

## Ordinary Assert review

Each annotation_plan key point is retained with its listed purpose and mathematical state. Upstream paths are a single entry, char/nonchar branch, or helper return as indicated; downstream work is the corresponding memory writes or helper calls. None merely duplicates an invariant or postcondition. Raw opening bridges opaque emitter ownership to builtin arrays and machine bounds; fragment openings expose exact callee plan shapes; temp transitions expose/refold function context and bridge concrete/semantic offsets. No loops, branch-control annotations, or higher-order existential witnesses are used.

## Iterations

1. Initial concrete instruction/emitter model and nine-function annotation candidate: design and symbolic execution passed. Read-only generated-VC review found branch-specific model type facts were omitted after full call-boundary assertions, making wrapper return obligations too weak.
2. Retain model_ty = CMCharTy or model_ty <> CMCharTy in the corresponding branch cut, derived from original encoded type equality and code-wf. Function contracts unchanged. Rerun checks.

## VC comparison

First attempt: no failed VC comparisons.

Final owner checks: two design checks, two symexec checks, and two post-symexec library checks all passed with process exit 0 and controller status passed. No failed tool/check invocations. The second design iteration was prompted by direct generated-VC semantic review, not a check failure. Current manual has 50 top-level VCs and 54 split declarations; no manual edits.
