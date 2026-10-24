# Character-byte conversion proof notes

Completed the three assigned pure split goals and their aggressive top-level dispatcher. The conversion proof specializes the existing `tower_machine_rem_byte__byte_encoding` lemma at index zero and simplifies the power, quotient, and encoder. The lower and upper byte bounds use `Z.mod_pos_bound`.

No new helper, import, or dependency was added. The previously verified shared library was only read and reused; it was not edited. New shared-dependency proof cost: zero.

Controller development compilation succeeded on its first invocation. The exact group wrapper also compiled on its first invocation. Failed check counts: development 0; debug 0 (not invoked); exact 0. There were no failed proof checks or proof-repair iterations. Final controller acceptance is separate from these preliminary compilation checks.
