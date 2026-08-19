import argparse
import contextlib
import io
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import blind_eval


SKILLS_ROOT = Path(__file__).resolve().parents[2]
SPECIALISTS = {
    domain: SKILLS_ROOT / skill_name
    for domain, skill_name in blind_eval.SPECIALIST_SKILLS.items()
}


class CorpusTests(unittest.TestCase):
    def test_numeric_selector_is_local_to_specialist(self) -> None:
        selected = blind_eval.resolve_example(SPECIALISTS["gkr-whir"], "12")
        self.assertEqual(selected.name, "12-dimension-reduction-index-space.md")

    def test_specialist_mapping(self) -> None:
        self.assertEqual(
            blind_eval.specialist_skill("transcript"),
            "zk-verifier-transcript-review",
        )
        with self.assertRaises(blind_eval.EvalError):
            blind_eval.specialist_skill("coordinator")

    def test_every_corpus_case_has_blindeval_metadata(self) -> None:
        examples = [
            (domain, path)
            for domain, skill in SPECIALISTS.items()
            for path in blind_eval.example_files(skill)
        ]
        self.assertEqual(len(examples), 65)
        parsed = [blind_eval.parse_example(path, domain) for domain, path in examples]
        self.assertTrue(all(item["paths"] for item in parsed))
        self.assertTrue(all(item["failure"] for item in parsed))
        self.assertTrue(all(item["impact_and_fix"] for item in parsed))
        self.assertEqual({item["domain"] for item in parsed}, set(SPECIALISTS))

    def test_strip_examples_removes_answer_corpus(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "skill"
            shutil.copytree(SPECIALISTS["transcript"], copied)
            blind_eval.strip_examples(copied)
            self.assertFalse((copied / "examples").exists())
            self.assertTrue((copied / "SKILL.md").is_file())

    def test_reference_support_is_not_a_discoverable_skill(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            injected = Path(directory) / "skills"
            injected.mkdir()
            support = blind_eval.inject_reference_support(
                SKILLS_ROOT, injected, "composition"
            )
            self.assertEqual(
                support,
                ["zk-verifier-review/references", "zk-circuit-review/references"],
            )
            self.assertFalse(any(injected.rglob("SKILL.md")))

    def test_prompt_invokes_only_selected_specialist(self) -> None:
        prompt = blind_eval.audit_prompt(
            "codex",
            "bounded target",
            "repository",
            "transcript",
            "zk-verifier-transcript-review",
        )
        self.assertIn("$zk-verifier-transcript-review", prompt)
        self.assertNotIn("$zk-verifier-review ", prompt)
        self.assertNotIn("monolith", prompt)


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
    def make_case(self, root: Path, *, contaminated: bool = False) -> Path:
        case = root / "case"
        run = case / "runs" / "run-1"
        fixture = case / "fixture"
        snapshot = case / "injected-skills"
        run.mkdir(parents=True)
        fixture.mkdir()
        snapshot.mkdir()
        (snapshot / "SKILL.md").write_text("fixture skills\n", encoding="utf-8")
        manifest = {
            "version": 6,
            "case_id": "case",
            "injected_skills_sha256": blind_eval.tree_digest(snapshot),
        }
        blind_eval.write_json(case / "manifest.json", manifest)
        blind_eval.write_json(
            run / "run.json",
            {
                "version": 4,
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

    def test_run_can_be_graded(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            result = self.grade(case, "catch", "same root freedom")
            grade = json.loads((case / "grade.json").read_text(encoding="utf-8"))
        self.assertEqual(result, 0)
        self.assertEqual(grade["run_schema_version"], 4)

    def test_cleanup_refuses_ungraded_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(argparse.Namespace(case_dir=case, force=False))

    def test_cleanup_refuses_contaminated_graded_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory), contaminated=True)
            self.grade(case, "unscored", "contaminated")
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(argparse.Namespace(case_dir=case, force=False))

    def test_cleanup_accepts_graded_clean_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            self.grade(case, "catch")
            with contextlib.redirect_stdout(io.StringIO()):
                blind_eval.cleanup(argparse.Namespace(case_dir=case, force=False))
            self.assertFalse((case / "fixture").exists())

    def test_cleanup_refuses_modified_skill_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            case = self.make_case(Path(directory))
            self.grade(case, "catch")
            (case / "injected-skills" / "SKILL.md").write_text(
                "modified skills\n", encoding="utf-8"
            )
            with self.assertRaises(blind_eval.EvalError):
                blind_eval.cleanup(argparse.Namespace(case_dir=case, force=False))


if __name__ == "__main__":
    unittest.main()
