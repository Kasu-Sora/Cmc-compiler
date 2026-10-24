# buffer-composition proof notes

Completed both assigned top-level VCs and all three assigned split goals. The buffer prefix is normalized by the standard preprocessing tactic; the return spatial goal rewrites the global emitter result using its existing postcondition before cancelling preserved resources. No new helper, definition or import was needed; the group library remains unchanged.

Development checks: 3, all failed during local tactic adjustment. The first removed redundant tactics after preprocessing had already closed the initial spatial split. The second restored the explicit return endpoint rewrite and cancellation. The third exposed the top-level branch order: aggressive preprocessing emits the spatial branch before the pure branch, so the two Goal_apply lines were reordered. One debug call inspected that branch order. The final exact group check passed on its first invocation. Controller acceptance remains separate.
