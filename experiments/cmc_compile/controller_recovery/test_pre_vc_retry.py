import sys, unittest
from pathlib import Path
from argparse import Namespace
from unittest.mock import patch
sys.path.insert(0, '/Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator')
sys.path.insert(0, '/Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/vc-proving')
from controller_attempts import retry_round, _failed_vcs_for_feedback
class PreVCDependencyRetry(unittest.TestCase):
    def test_no_vcs_does_not_read_missing_manual(self):
        with patch('controller_attempts._find_group_attempt', return_value=None), patch('controller_attempts._find_round_attempt', return_value={'phase':'annotation'}), patch('controller_attempts._validated_annotation_attempt_paths') as paths:
            self.assertEqual(_failed_vcs_for_feedback({}, 'a', {'blocker':{'failure_class':'dependency-gap','vcs':[]}}), [])
            paths.assert_not_called()
    def test_named_vcs_still_require_manual(self):
        with patch('controller_attempts._find_group_attempt', return_value=None), patch('controller_attempts._find_round_attempt', return_value={'phase':'annotation'}), patch('controller_attempts._validated_annotation_attempt_paths', return_value={'after':Path('/nonexistent-cmc-regression')}):
            with self.assertRaises(FileNotFoundError):
                _failed_vcs_for_feedback({'target_files':{'proof_manual_file':'manual.v'}}, 'a', {'blocker':{'failure_class':'dependency-gap','vcs':[{'name':'x'}]}})
    def test_pre_vc_dependency_retry_keeps_annotation_session(self):
        source_phase="annotation"
        source_id="Case-annotation-r1-attempt-1"
        reason="annotation-blocked"
        aggregate=False
        previous = {
            "attempt_id": "Case-annotation-r1-attempt-1",
            "round": "Case-annotation-r1",
            "phase": "annotation",
            "status": "accepted",
            "failed_vcs": [],
        }
        source = {
            "attempt_id": source_id,
            "round": source_id,
            "phase": source_phase,
            "status": "blocked",
        }
        blocker = {
            "failure_class": "dependency-gap",
            "kind": "missing-annotation-premise",
            "vcs": [],
            "message": "missing result premise",
            "repair_boundary": "loop invariant",
        }
        failed = {
            "source_attempt": source_id,
            "name": "proof_of_x",
            "parent": None,
            "annotation_location": "loop exit",
            "manual": "/run/sealed.v",
            "manual_sha256": "b" * 64,
            "statement_sha256": "c" * 64,
            "message": "missing result premise",
        }
        state = {
            "attempts": {
                previous["attempt_id"]: previous,
                source_id: source,
            },
            "next_actions": [
                {
                    "kind": "main-owned-action",
                    "action": "retry-round",
                    "phase": "annotation",
                    "reason": reason,
                    "previous_attempt": source_id,
                }
            ],
            "annotation_session": {
                "session_id": "Case-annotation-agent",
                "current_attempt": previous["attempt_id"],
            },
        }
        created_id = "Case-annotation-r2-attempt-1"

        def create_attempt(selected_state: dict[str, object], **_kwargs: object) -> dict[str, object]:
            created = {
                "attempt_id": created_id,
                "round": "Case-annotation-r2",
                "phase": "annotation",
                "status": "prepared",
            }
            selected_state["attempts"][created_id] = created
            return created

        with (
            patch("controller_attempts._run_root_from_id", return_value=Path("/run")),
            patch("controller_attempts._load_state", return_value=state),
            patch("controller_attempts._running_deliveries", return_value=[]),
            patch("controller_attempts._current_annotation_attempt", return_value=previous),
            patch("controller_attempts._annotation_after_snapshot_errors", return_value=[]),
            patch(
                "controller_attempts._feedback_sources_for_retry",
                return_value=(
                    [{"attempt_id": source_id}],
                    [{"status": "blocked", "blocker": blocker}],
                    [blocker] if aggregate else [],
                    [],
                ),
            ),
            patch("controller_attempts._failed_vcs_errors", return_value=[]),
            patch("controller_attempts._unresolved_failed_vcs", return_value=[]),
            patch("controller_attempts._vc_comparison_history", return_value=[]),
            patch("controller_attempts._attempt_artifact", return_value=Path("/artifact")),
            patch(
                "controller_attempts._validated_annotation_attempt_paths",
                return_value={"plan": Path("/plan")},
            ),
            patch("controller_attempts._invalidate_downstream"),
            patch("controller_attempts._init_round_attempt", side_effect=create_attempt),
            patch("controller_attempts._append_event"),
            patch("controller_attempts._save_state"),
            patch("builtins.print"),
        ):
            self.assertEqual(
                retry_round(
                    Namespace(
                        main_root="/workspace",
                        run="run",
                        phase="annotation",
                        reason=reason,
                        previous_attempt=source_id,
                    )
                ),
                0,
            )
        self.assertIn(created_id, state["attempts"])
        self.assertEqual(state["attempts"][created_id]["retry_reason"], reason)
        self.assertEqual(
            state["attempts"][created_id]["retry_previous_attempt"],
            source_id,
        )


if __name__ == '__main__': unittest.main()
