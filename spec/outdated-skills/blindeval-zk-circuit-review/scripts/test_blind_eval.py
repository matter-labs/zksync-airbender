import argparse
import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

import blind_eval


class TraceInspectionTests(unittest.TestCase):
    def test_forwarded_subagent_web_search_is_contamination(self) -> None:
        event = {
            "type": "stream_event",
            "parent_tool_use_id": "toolu_parent_agent",
            "event": {
                "type": "content_block_start",
                "content_block": {
                    "type": "tool_use",
                    "name": "WebSearch",
                    "input": {"query": "zksync-airbender historical fix"},
                },
            },
        }
        with tempfile.TemporaryDirectory() as directory:
            events = Path(directory) / "events.jsonl"
            events.write_text(json.dumps(event) + "\n", encoding="utf-8")
            findings = blind_eval.inspect_contamination(
                events, "claude", ["zksync-airbender"]
            )
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["request"]["name"], "WebSearch")


class LifecycleTests(unittest.TestCase):
    def make_case(
        self, root: Path, *, contaminated: bool = False, manifest_version: int = 1
    ) -> Path:
        case = root / "case"
        run = case / "runs" / "run-1"
        fixture = case / "fixture"
        run.mkdir(parents=True)
        fixture.mkdir()
        manifest = {"version": manifest_version, "case_id": "case"}
        if manifest_version >= 4:
            snapshot = case / "injected-skill"
            snapshot.mkdir()
            (snapshot / "SKILL.md").write_text("fixture skill\n", encoding="utf-8")
        if manifest_version >= 5:
            manifest["injected_skill_sha256"] = blind_eval.tree_digest(snapshot)
        blind_eval.write_json(case / "manifest.json", manifest)
        blind_eval.write_json(
            run / "run.json",
            {
                "version": 2,
                "returncode": 0,
                "timed_out": False,
                "contaminated": contaminated,
                "contamination": [{"reason": "test"}] if contaminated else [],
                "final_message_present": True,
            },
        )
        return case

    def grade(self, case: Path, outcome: str, notes: str = "") -> int:
        with contextlib.redirect_stdout(io.StringIO()):
            return blind_eval.grade(
                argparse.Namespace(
                    case_dir=case, outcome=outcome, notes=notes, replace=False
                )
            )

    def test_schema_v2_run_can_be_graded(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            result = self.grade(case, "catch", "legacy")
            grade = json.loads((case / "grade.json").read_text(encoding="utf-8"))
        self.assertEqual(result, 0)
        self.assertEqual(grade["run_schema_version"], 2)

    def test_cleanup_refuses_ungraded_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(
                    argparse.Namespace(
                        case_dir=case,
                        force=False,
                    )
                )

    def test_cleanup_refuses_contaminated_graded_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory), contaminated=True)
            self.grade(case, "unscored", "contaminated")
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(
                    argparse.Namespace(
                        case_dir=case,
                        force=False,
                    )
                )

    def test_cleanup_accepts_graded_clean_case_without_confirmation_flag(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            self.grade(case, "catch")
            with contextlib.redirect_stdout(io.StringIO()):
                blind_eval.cleanup(
                    argparse.Namespace(
                        case_dir=case,
                        force=False,
                    )
                )
            self.assertFalse((case / "fixture").exists())

    def test_cleanup_refuses_grade_for_another_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            self.grade(case, "catch")
            grade_path = case / "grade.json"
            grade = json.loads(grade_path.read_text(encoding="utf-8"))
            grade["case_id"] = "another-case"
            blind_eval.write_json(grade_path, grade)
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(argparse.Namespace(case_dir=case, force=False))

    def test_cleanup_refuses_modified_skill_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory), manifest_version=5)
            self.grade(case, "catch")
            (case / "injected-skill" / "SKILL.md").write_text(
                "modified skill\n", encoding="utf-8"
            )
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(argparse.Namespace(case_dir=case, force=False))


if __name__ == "__main__":
    unittest.main()
