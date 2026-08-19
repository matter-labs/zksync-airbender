#!/usr/bin/env python3
"""Blind-evaluate a verifier-review monolith or coordinator against one case."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path
from typing import Any, Iterable


CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9._-]*\Z")
CORPUS_SKILL_NAME = "zk-verifier-review-monolith"
MONOLITH_SKILLS = [CORPUS_SKILL_NAME]
COORDINATOR_SKILLS = [
    "zk-verifier-review",
    "zk-verifier-transcript-review",
    "zk-verifier-composition-review",
    "zk-gkr-whir-verifier-review",
    "zk-stark-fri-verifier-review",
    "zk-verifier-soundness-review",
    "zk-recursion-l1-verifier-review",
]


class EvalError(RuntimeError):
    pass


def run_checked(
    command: list[str],
    *,
    cwd: Path | None = None,
    text: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[Any]:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=text,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        check=False,
    )
    if result.returncode:
        stderr = result.stderr.strip() if text else result.stderr.decode(errors="replace").strip()
        raise EvalError(f"command failed ({result.returncode}): {' '.join(command)}\n{stderr}")
    return result


def git(repo: Path, *args: str) -> str:
    return run_checked(["git", "-C", str(repo), *args]).stdout.strip()


def resolve_repo(path: Path) -> Path:
    return Path(git(path.resolve(), "rev-parse", "--show-toplevel")).resolve()


def resolve_commit(repo: Path, ref: str) -> str:
    return git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}")


def repository_markers(repo: Path) -> list[str]:
    markers = {repo.name.casefold()}
    for remote in git(repo, "remote").splitlines():
        url = git(repo, "remote", "get-url", remote).strip().rstrip("/")
        if not url:
            continue
        normalized = re.sub(r"\.git$", "", url, flags=re.I)
        markers.add(normalized.casefold())
        without_scheme = re.sub(r"^[a-z][a-z0-9+.-]*://", "", normalized, flags=re.I)
        markers.add(without_scheme.casefold())
        if ":" in without_scheme and "/" not in without_scheme.split(":", 1)[0]:
            without_scheme = without_scheme.replace(":", "/", 1)
        parts = without_scheme.split("/", 1)
        if len(parts) == 2:
            markers.add(parts[1].casefold())
    return sorted(marker for marker in markers if marker)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat()


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def tree_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix().encode()
        digest.update(relative + b"\0")
        if path.is_symlink():
            digest.update(b"L\0" + os.readlink(path).encode() + b"\0")
        elif path.is_file():
            digest.update(b"F\0")
            with path.open("rb") as handle:
                for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                    digest.update(chunk)
        elif path.is_dir():
            digest.update(b"D\0")
    return digest.hexdigest()


def load_manifest(case_dir: Path) -> dict[str, Any]:
    path = case_dir / "manifest.json"
    if not path.is_file():
        raise EvalError(f"missing manifest: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def safe_extract(archive: Path, destination: Path) -> None:
    with tarfile.open(archive, "r:") as handle:
        for member in handle.getmembers():
            name = Path(member.name)
            if name.is_absolute() or ".." in name.parts:
                raise EvalError(f"unsafe archive member: {member.name}")
        try:
            handle.extractall(destination, filter="data")
        except TypeError:  # Python < 3.12
            handle.extractall(destination)


def remove_path(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)


def strip_agent_artifacts(fixture: Path) -> None:
    for directory_name in [".claude", ".codex"]:
        paths = sorted(
            fixture.rglob(directory_name), key=lambda path: len(path.parts), reverse=True
        )
        for path in paths:
            remove_path(path)
    for agents in sorted(
        fixture.rglob(".agents"), key=lambda path: len(path.parts), reverse=True
    ):
        if not agents.is_dir() or agents.is_symlink():
            continue
        for name in ["skills", "plans", "specs", "audits", "output", ".bus"]:
            remove_path(agents / name)
    for path in sorted(
        fixture.rglob(".git"), key=lambda path: len(path.parts), reverse=True
    ):
        remove_path(path)


def example_files(skill: Path) -> list[Path]:
    examples = skill / "examples"
    if not examples.is_dir():
        return []
    return sorted(
        path
        for path in examples.glob("*/*.md")
        if path.name != "INDEX.md" and re.match(r"^[0-9]+-", path.name)
    )


def slugify(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


def example_title(path: Path) -> str:
    first_line = path.read_text(encoding="utf-8", errors="replace").splitlines()[0]
    if not first_line.startswith("# "):
        raise EvalError(f"example has no H1 title: {path}")
    return first_line[2:].strip()


def resolve_example(skill: Path, selector: str) -> Path:
    files = example_files(skill)
    if not files:
        raise EvalError(f"skill has no examples: {skill}")
    raw = selector.strip().replace(":", "/")
    domains = {path.parent.name for path in files}
    domain: str | None = None
    if "/" in raw:
        candidate_domain, raw = raw.split("/", 1)
        if candidate_domain not in domains:
            raise EvalError(
                f"unknown example domain {candidate_domain!r}; choose from {', '.join(sorted(domains))}"
            )
        domain = candidate_domain
        files = [path for path in files if path.parent.name == domain]
    numeric = re.fullmatch(r"#?0*([0-9]+)", raw)

    def matching(candidates: Iterable[Path]) -> list[Path]:
        if numeric:
            prefix = f"{int(numeric.group(1)):02d}-"
            return [path for path in candidates if path.name.startswith(prefix)]

        basename = Path(raw).name.casefold()
        normalized = slugify(raw)
        result: list[Path] = []
        for path in candidates:
            stem_without_number = re.sub(r"^[0-9]+-", "", path.stem)
            title = example_title(path)
            if (
                basename in {path.name.casefold(), path.stem.casefold()}
                or normalized in {slugify(stem_without_number), slugify(title)}
                or raw.casefold() == title.casefold()
            ):
                result.append(path)
        return result

    matches = matching(files)
    if len(matches) != 1:
        examples_root = skill / "examples"
        names = ", ".join(
            path.relative_to(examples_root).as_posix() for path in matches
        ) or "none"
        raise EvalError(f"example selector {selector!r} matched {len(matches)} examples: {names}")
    return matches[0]


def parse_example(path: Path) -> dict[str, Any]:
    content = path.read_text(encoding="utf-8", errors="replace")
    title = example_title(path)
    def field(pattern: str, label: str) -> str:
        match = re.search(pattern, content, re.MULTILINE)
        if not match:
            raise EvalError(f"example {path.name} has no {label}")
        return match.group(1).strip()

    fixed_line = field(
        r"^- Fixed(?: in merged history)? by:\s*(.+)$", "Fixed by field"
    )
    fix_candidates = re.findall(r"(?<![0-9a-f])[0-9a-f]{7,40}(?![0-9a-f])", fixed_line, re.I)
    if not fix_candidates:
        raise EvalError(f"example {path.name} has no fix commit")
    fix_ref = max(fix_candidates, key=len)
    vulnerable_ref = field(
        r"^- Vulnerable revision(?: for reproduction)?:\s*`([0-9a-f]{7,40})`\s*$",
        "vulnerable revision",
    )
    paths: list[str] = []
    for line in content.splitlines():
        command = line.strip()
        if not command.startswith("git diff "):
            continue
        tokens = shlex.split(command)
        if "--" in tokens:
            paths.extend(tokens[tokens.index("--") + 1 :])
    paths = list(dict.fromkeys(path for path in paths if "/" in path))
    if not paths:
        raise EvalError(f"example {path.name} has no affected reproduction paths")

    def section(name: str) -> str:
        match = re.search(
            rf"(?ms)^## {re.escape(name)}\s*\n(.*?)(?=^## |\Z)", content
        )
        return match.group(1).strip() if match else ""

    domain = path.parent.name
    component = f"{domain} verifier/argument component"
    target = f"{component}; affected historical paths: {', '.join(paths)}"
    return {
        "name": path.name,
        "domain": domain,
        "selector": f"{domain}/{path.name}",
        "title": title,
        "fix_ref": fix_ref,
        "vulnerable_ref": vulnerable_ref,
        "component": component,
        "paths": paths,
        "target": target,
        "failure": section("Failure"),
        "impact_and_fix": section("Impact and fix"),
    }


def strip_examples(skill: Path) -> None:
    remove_path(skill / "examples")


def scan_skill(skill: Path, patterns: Iterable[tuple[str, re.Pattern[str]]]) -> list[str]:
    findings: list[str] = []
    for path in sorted(skill.rglob("*")):
        if not path.is_file() or path.is_symlink():
            continue
        content = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in patterns:
            if pattern.search(content):
                findings.append(f"{path.relative_to(skill)}: {label}")
    return findings


def assert_safe_symlinks(fixture: Path) -> None:
    root = fixture.resolve()
    for path in fixture.rglob("*"):
        if not path.is_symlink():
            continue
        target = (path.parent / os.readlink(path)).resolve(strict=False)
        try:
            target.relative_to(root)
        except ValueError as error:
            raise EvalError(f"symlink escapes fixture: {path} -> {os.readlink(path)}") from error


def initialize_singleton_repo(fixture: Path) -> None:
    run_checked(["git", "init", "--quiet", "--initial-branch=eval"], cwd=fixture)
    run_checked(["git", "add", "-A"], cwd=fixture)
    env = os.environ.copy()
    env.update(
        {
            "GIT_AUTHOR_NAME": "Blind Evaluation",
            "GIT_AUTHOR_EMAIL": "eval@invalid",
            "GIT_COMMITTER_NAME": "Blind Evaluation",
            "GIT_COMMITTER_EMAIL": "eval@invalid",
            "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
            "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
        }
    )
    run_checked(["git", "commit", "--quiet", "-m", "evaluation snapshot"], cwd=fixture, env=env)
    git(fixture, "config", "gc.auto", "0")


def verification_errors(case_dir: Path, manifest: dict[str, Any]) -> list[str]:
    fixture = (case_dir / "fixture").resolve()
    errors: list[str] = []
    if not fixture.is_dir():
        return [f"fixture is missing: {fixture}"]
    checks = {
        "commit count": ("1", lambda: git(fixture, "rev-list", "--all", "--count")),
        "remotes": ("", lambda: git(fixture, "remote")),
        "status": ("", lambda: git(fixture, "status", "--porcelain")),
        "refs": ("refs/heads/eval", lambda: git(fixture, "for-each-ref", "--format=%(refname)")),
    }
    for label, (expected, operation) in checks.items():
        try:
            actual = operation()
        except EvalError as error:
            errors.append(f"{label}: {error}")
            continue
        if actual != expected:
            errors.append(f"{label}: expected {expected!r}, got {actual!r}")
    if (fixture / ".git" / "objects" / "info" / "alternates").exists():
        errors.append("Git object alternates are present")
    config = (fixture / ".git" / "config").read_text(encoding="utf-8", errors="replace")
    if re.search(r"\burl\s*=|alternate", config, re.I):
        errors.append("Git config contains an external URL or alternate")
    if (fixture / ".codex").exists():
        errors.append("unexpected .codex directory")
    if manifest.get("version", 1) >= 3:
        markers = manifest.get("forbidden_repository_markers")
        label = str(manifest.get("repository_label", "")).casefold()
        if not isinstance(markers, list) or not markers:
            errors.append("audited-repository contamination markers are missing")
        elif label and label not in markers:
            errors.append("repository label is missing from contamination markers")
    claude_skills = fixture / ".claude" / "skills"
    if not claude_skills.is_symlink() or os.readlink(claude_skills) != "../.agents/skills":
        errors.append("Claude shared-skills symlink is missing or incorrect")
    skills_root = fixture / ".agents" / "skills"
    expected_skill_names = manifest.get("injected_skill_names", [])
    if not isinstance(expected_skill_names, list) or not expected_skill_names:
        errors.append("injected skill names are missing")
    for name in expected_skill_names:
        skill = skills_root / name
        if not (skill / "SKILL.md").is_file():
            errors.append(f"injected skill is missing: {name}")
        if (skill / "examples").exists():
            errors.append(f"historical examples remain in injected skill: {name}")

    snapshot = case_dir / "injected-skills"
    if not snapshot.is_dir():
        errors.append("injected skills snapshot is missing")
    else:
        expected_digest = manifest.get("injected_skills_sha256")
        if not isinstance(expected_digest, str):
            errors.append("injected skills digest is missing")
        else:
            if tree_digest(snapshot) != expected_digest:
                errors.append("injected skills snapshot digest mismatch")
            if tree_digest(skills_root) != expected_digest:
                errors.append("fixture injected skills digest mismatch")
    patterns: list[tuple[str, re.Pattern[str]]] = []
    for commit in [manifest["fix_commit"]]:
        patterns.extend(
            [
                ("fix commit", re.compile(re.escape(commit), re.I)),
                (
                    "short fix commit",
                    re.compile(
                        rf"(?<![0-9a-f]){re.escape(commit[:7])}(?![0-9a-f])", re.I
                    ),
                ),
            ]
        )
    for value in manifest["forbidden_patterns"]:
        try:
            patterns.append((f"forbidden regex {value!r}", re.compile(value, re.I)))
        except re.error as error:
            errors.append(f"invalid forbidden regex {value!r}: {error}")
    errors.extend(
        f"skill contamination: {item}" for item in scan_skill(skills_root, patterns)
    )
    try:
        assert_safe_symlinks(fixture)
    except EvalError as error:
        errors.append(str(error))
    return errors


def prepare(args: argparse.Namespace) -> int:
    repo = resolve_repo(args.repo)
    skills_source_root = (args.skills_root or repo / ".agents" / "skills").resolve()
    corpus_skill = (
        args.corpus_skill or skills_source_root / CORPUS_SKILL_NAME
    ).resolve()
    if not (corpus_skill / "SKILL.md").is_file():
        raise EvalError(f"invalid verifier-review corpus skill: {corpus_skill}")
    selected_path = resolve_example(corpus_skill, args.example)
    selected = parse_example(selected_path)
    fix_commit = resolve_commit(repo, selected["fix_ref"])
    source_commit = resolve_commit(repo, selected["vulnerable_ref"])
    repo_markers = repository_markers(repo)

    skill_names = MONOLITH_SKILLS if args.reviewer == "monolith" else COORDINATOR_SKILLS
    skill_sources = [skills_source_root / name for name in skill_names]
    missing = [str(path) for path in skill_sources if not (path / "SKILL.md").is_file()]
    if missing:
        raise EvalError("missing reviewer skill(s): " + ", ".join(missing))

    case_id = args.case_id or (
        f"{args.reviewer}-{selected['domain']}-{selected_path.stem}-"
        f"{dt.datetime.now().strftime('%Y%m%d-%H%M%S')}"
    )
    if not CASE_ID_RE.fullmatch(case_id):
        raise EvalError("case-id must contain only lowercase letters, digits, '.', '_', or '-'")
    output_root = (
        args.output_root
        or repo / ".agents" / "output" / "blindeval-zk-verifier-review"
    ).resolve()
    case_dir = output_root / case_id
    if case_dir.exists():
        raise EvalError(f"case directory already exists: {case_dir}")
    output_root.mkdir(parents=True, exist_ok=True)

    staging = Path(tempfile.mkdtemp(prefix=f".{case_id}.", dir=output_root))
    try:
        fixture = staging / "fixture"
        fixture.mkdir()
        archive = staging / "source.tar"
        run_checked(
            ["git", "-C", str(repo), "archive", "--format=tar", f"--output={archive}", source_commit]
        )
        safe_extract(archive, fixture)
        archive.unlink()
        strip_agent_artifacts(fixture)

        injected_root = fixture / ".agents" / "skills"
        injected_root.mkdir(parents=True, exist_ok=True)
        for source_skill, skill_name in zip(skill_sources, skill_names, strict=True):
            injected = injected_root / skill_name
            shutil.copytree(source_skill, injected, symlinks=True)
            strip_examples(injected)
        injected_skills_snapshot = staging / "injected-skills"
        shutil.copytree(injected_root, injected_skills_snapshot, symlinks=True)
        injected_skills_digest = tree_digest(injected_skills_snapshot)

        shutil.copy2(selected_path, staging / "answer-key.md")

        claude = fixture / ".claude"
        claude.mkdir()
        (claude / "skills").symlink_to("../.agents/skills")
        assert_safe_symlinks(fixture)
        initialize_singleton_repo(fixture)

        manifest = {
            "version": 6,
            "case_id": case_id,
            "created_at": utc_now(),
            "repo_root": str(repo),
            "reviewer": args.reviewer,
            "selected_example": selected["selector"],
            "selected_example_title": selected["title"],
            "selected_example_domain": selected["domain"],
            "source_ref": selected["vulnerable_ref"],
            "source_commit": source_commit,
            "fix_ref": selected["fix_ref"],
            "fix_commit": fix_commit,
            "target": selected["target"],
            "target_component": selected["component"],
            "target_paths": selected["paths"],
            "answer_key": "answer-key.md",
            "repository_label": repo.name,
            "forbidden_repository_markers": sorted(
                set(repo_markers)
                | {path.casefold() for path in selected["paths"]}
                | {
                    selected["title"].casefold(),
                    source_commit.casefold(),
                    fix_commit.casefold(),
                }
            ),
            "corpus_skill_source": str(corpus_skill),
            "injected_skill_names": skill_names,
            "injected_skill_sources": [str(path) for path in skill_sources],
            "injected_skills_snapshot": "injected-skills",
            "injected_skills_sha256": injected_skills_digest,
            "forbidden_patterns": [re.escape(selected["title"])],
        }
        write_json(staging / "manifest.json", manifest)
        errors = verification_errors(staging, manifest)
        if errors:
            raise EvalError("fixture verification failed:\n- " + "\n- ".join(errors))
        staging.rename(case_dir)
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise

    print(
        json.dumps(
            {
                "case_dir": str(case_dir),
                "fixture": str(case_dir / "fixture"),
                "reviewer": args.reviewer,
                "selected_example": selected["selector"],
                "source_commit": source_commit,
                "fix_commit": fix_commit,
                "target": selected["target"],
                "injected_skill_names": skill_names,
                "answer_key": str(case_dir / "answer-key.md"),
                "verification": "passed",
            },
            indent=2,
        )
    )
    return 0


def verify(args: argparse.Namespace) -> int:
    case_dir = args.case_dir.resolve()
    manifest = load_manifest(case_dir)
    errors = verification_errors(case_dir, manifest)
    result = {"case_dir": str(case_dir), "verification": "failed" if errors else "passed", "errors": errors}
    print(json.dumps(result, indent=2))
    return 2 if errors else 0


def mkdirs(path: Path, *relative: str) -> None:
    for value in relative:
        (path / value).mkdir(parents=True, exist_ok=True)


def minimal_bwrap(
    fixture: Path, runtime_home: Path, provider: str, settings: Path | None
) -> list[str]:
    bwrap = shutil.which("bwrap")
    if not bwrap:
        raise EvalError("bubblewrap is required; refusing an unsandboxed fallback")
    command = [
        bwrap,
        "--die-with-parent",
        "--new-session",
        "--unshare-pid",
        "--unshare-ipc",
        "--unshare-uts",
        "--tmpfs",
        "/",
    ]
    for source in [Path("/usr"), Path("/etc"), Path("/opt"), Path("/run"), Path("/mnt/wsl")]:
        if source.exists():
            command += ["--dir", str(source), "--ro-bind", str(source), str(source)]
    for link, target in [("/bin", "usr/bin"), ("/sbin", "usr/sbin"), ("/lib", "usr/lib"), ("/lib64", "usr/lib64")]:
        command += ["--symlink", target, link]
    command += [
        "--dir",
        "/home",
        "--dir",
        "/home/eval",
        "--bind",
        str(runtime_home),
        "/home/eval",
        "--dir",
        "/workspace",
        "--bind",
        str(fixture),
        "/workspace",
        "--dir",
        "/proc",
        "--proc",
        "/proc",
        "--dir",
        "/dev",
        "--dev",
        "/dev",
        "--dir",
        "/tmp",
        "--tmpfs",
        "/tmp",
    ]

    host_home = Path.home()
    tool_mounts = [
        (host_home / ".rustup", Path("/home/eval/.rustup")),
        (host_home / ".cargo" / "bin", Path("/home/eval/.cargo/bin")),
        (host_home / ".cargo" / "registry", Path("/home/eval/.cargo/registry")),
    ]
    for source, target in tool_mounts:
        if source.exists():
            command += ["--dir", str(target), "--ro-bind", str(source), str(target)]

    if provider == "codex":
        auth = host_home / ".codex" / "auth.json"
        target = Path("/home/eval/.codex/auth.json")
    else:
        auth = host_home / ".claude" / ".credentials.json"
        target = Path("/home/eval/.claude/.credentials.json")
    if auth.is_file():
        command += ["--ro-bind", str(auth), str(target)]
    elif provider == "codex" and not (os.getenv("CODEX_API_KEY") or os.getenv("OPENAI_API_KEY")):
        raise EvalError("Codex credentials are unavailable")
    elif provider == "claude" and not os.getenv("ANTHROPIC_API_KEY"):
        raise EvalError("Claude credentials are unavailable")

    command += [
        "--clearenv",
        "--setenv",
        "HOME",
        "/home/eval",
        "--setenv",
        "USER",
        "eval",
        "--setenv",
        "LOGNAME",
        "eval",
        "--setenv",
        "LANG",
        os.getenv("LANG", "C.UTF-8"),
        "--setenv",
        "PATH",
        "/home/eval/.cargo/bin:/usr/local/bin:/usr/bin:/bin",
        "--setenv",
        "CARGO_HOME",
        "/home/eval/.cargo",
        "--setenv",
        "RUSTUP_HOME",
        "/home/eval/.rustup",
        "--setenv",
        "CARGO_NET_OFFLINE",
        "true",
        "--chdir",
        "/workspace",
        "--",
    ]
    for name in ["CODEX_API_KEY", "OPENAI_API_KEY", "ANTHROPIC_API_KEY"]:
        if os.getenv(name):
            insert_at = command.index("--chdir")
            command[insert_at:insert_at] = ["--setenv", name, os.environ[name]]
    return command


def audit_prompt(
    provider: str, target: str, repository_label: str, reviewer: str
) -> str:
    skill_name = (
        "zk-verifier-review-monolith" if reviewer == "monolith" else "zk-verifier-review"
    )
    invocation = f"${skill_name}" if provider == "codex" else f"/{skill_name}"
    return (
        f"Use {invocation} to perform an authorized, defensive, read-only verifier-soundness review of exactly this historical target: "
        f"{target}\n\n"
        "Inspect every protocol, transcript, generated-artifact, composition, or acceptance dependency "
        "needed to decide this bounded target, while stating explicit coverage limits. Follow the skill's "
        "evidence gate and reporting format. Use only minimal bounded symbolic assignments or abstract "
        "proof flows needed to establish a verifier mismatch. Do not generate or "
        "execute proof-generation exploits, attack scripts, operational reproduction procedures, "
        "deployment payloads, network probes, credential/access steps, or instructions for targeting "
        "a live system. Broad external research is allowed, including source-hosting sites, for "
        "normative standards, cryptographic background, auditing techniques, and unrelated reference "
        "implementations. Do not externally search for, fetch, or consult the audited project "
        f"({repository_label}) or any copy, mirror, newer source version, commit, diff, issue, pull "
        "request, patch, changelog, or vulnerability report concerning that project. Base all "
        "project-specific conclusions on the provided "
        "snapshot. Recommend the missing invariant and a defensive regression property."
    )


def claude_settings(path: Path) -> None:
    settings = {
        "permissions": {
            "allow": ["Read", "Glob", "Grep", "Bash", "Agent", "WebSearch", "WebFetch"],
            "deny": [
                "Read(/home/eval/.claude/**)",
                "Edit(/home/eval/.claude/**)",
                "Write(/home/eval/.claude/**)",
            ],
        },
        "sandbox": {
            "enabled": True,
            "autoAllowBashIfSandboxed": True,
            "allowUnsandboxedCommands": False,
            "failIfUnavailable": True,
            "filesystem": {
                "denyRead": ["/home/eval/.claude"],
                "allowRead": ["/workspace"],
            },
        },
    }
    write_json(path, settings)


def provider_command(args: argparse.Namespace, prompt: str, settings: Path | None) -> list[str]:
    if args.provider == "codex":
        command = [
            "/usr/local/bin/codex",
            "exec",
            "--cd",
            "/workspace",
            "--ephemeral",
            "--ignore-user-config",
            "--ignore-rules",
            "--strict-config",
            "--sandbox",
            "workspace-write",
            "--json",
            "--disable",
            "apps",
            "--disable",
            "plugins",
            "--disable",
            "memories",
            "--disable",
            "skill_mcp_dependency_install",
            "--disable",
            "browser_use",
            "--disable",
            "browser_use_external",
            "--disable",
            "computer_use",
            "-c",
            'approval_policy="never"',
            "-c",
            'history.persistence="none"',
            "-c",
            "hide_agent_reasoning=false",
            "-c",
            "show_raw_agent_reasoning=true",
            "-c",
            'web_search="live"',
            "-c",
            "sandbox_workspace_write.network_access=false",
            "-c",
            'permissions.filesystem.deny_read=["/home/eval/.codex"]',
        ]
        if args.model:
            command += ["--model", args.model]
        if args.effort:
            command += ["-c", f'model_reasoning_effort="{args.effort}"']
        return command + [prompt]

    assert settings is not None
    command = [
        "/usr/local/bin/claude",
        "--print",
        "--output-format",
        "stream-json",
        "--verbose",
        "--include-partial-messages",
        "--forward-subagent-text",
        "--no-session-persistence",
        "--no-chrome",
        "--setting-sources",
        "project",
        "--settings",
        "/home/eval/eval-settings.json",
        "--strict-mcp-config",
        "--mcp-config",
        '{"mcpServers":{}}',
        "--permission-mode",
        "dontAsk",
        "--disallowedTools=Edit,Write,NotebookEdit",
    ]
    if args.model:
        command += ["--model", args.model]
    if args.effort:
        command += ["--effort", args.effort]
    return command + [prompt]


def tool_requests(provider: str, event: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    requests: list[tuple[str, dict[str, Any]]] = []
    if provider == "codex":
        item = event.get("item")
        if not isinstance(item, dict):
            return requests
        item_type = item.get("type")
        if item_type == "web_search":
            requests.append(
                ("web", {key: item[key] for key in ("query", "action") if key in item})
            )
        elif item_type == "command_execution":
            requests.append(("command", {"command": item.get("command", "")}))
        elif item_type == "mcp_tool_call":
            requests.append(
                (
                    "mcp",
                    {
                        key: item[key]
                        for key in ("server", "tool", "name", "arguments", "input")
                        if key in item
                    },
                )
            )
    else:
        pending: list[Any] = [event]
        while pending:
            value = pending.pop()
            if isinstance(value, list):
                pending.extend(value)
                continue
            if not isinstance(value, dict):
                continue
            if value.get("type") == "tool_use":
                name = str(value.get("name", ""))
                request = {"name": name, "input": value.get("input", {})}
                if name in {"WebSearch", "WebFetch"}:
                    requests.append(("web", request))
                elif name == "Bash":
                    requests.append(("command", request))
                elif name.startswith("mcp__"):
                    requests.append(("mcp", request))
            pending.extend(value.values())
    return requests


def inspect_contamination(
    events_path: Path, provider: str, forbidden_markers: Iterable[str] = ()
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    markers = sorted({marker.casefold() for marker in forbidden_markers if marker})
    for number, line in enumerate(events_path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        for request_kind, request in tool_requests(provider, event):
            rendered = json.dumps(request, sort_keys=True)
            reasons: list[str] = []
            rendered_folded = rendered.casefold()
            network_command = request_kind == "command" and bool(
                re.search(
                    r"\b(?:curl|wget|aria2c|httpie|gh)\b|"
                    r"\bgit\s+(?:clone|fetch|pull|remote\s+add)\b",
                    rendered,
                    re.I,
                )
            )
            externally_resolved = request_kind in {"web", "mcp"} or network_command
            matched = (
                [marker for marker in markers if marker in rendered_folded]
                if externally_resolved
                else []
            )
            if matched:
                reasons.append("audited-repository external lookup")
            if reasons:
                findings.append(
                    {
                        "line": number,
                        "reasons": reasons,
                        "matched_markers": matched,
                        "request": request,
                    }
                )
    return findings


def extract_final(events_path: Path, provider: str) -> str:
    final = ""
    for line in events_path.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if provider == "codex":
            item = event.get("item")
            if (
                event.get("type") == "item.completed"
                and isinstance(item, dict)
                and item.get("type") == "agent_message"
            ):
                final = item.get("text", final)
        elif event.get("type") == "result" and isinstance(event.get("result"), str):
            candidate = event["result"]
            # Claude can emit a late background-agent result after the main audit.
            # Preserve the substantive report instead of blindly taking the last result.
            if len(candidate.strip()) > len(final.strip()):
                final = candidate
    return final


def run_eval(args: argparse.Namespace) -> int:
    case_dir = args.case_dir.resolve()
    manifest = load_manifest(case_dir)
    errors = verification_errors(case_dir, manifest)
    if errors:
        raise EvalError("fixture verification failed:\n- " + "\n- ".join(errors))

    runs_dir = case_dir / "runs"
    try:
        runs_dir.mkdir()
    except FileExistsError as error:
        raise EvalError(
            "fixture is single-use and already has a run attempt; prepare a fresh case"
        ) from error
    run_id = f"{dt.datetime.now().strftime('%Y%m%d-%H%M%S')}-{args.provider}"
    run_dir = runs_dir / run_id
    run_dir.mkdir()
    runtime_home = Path(tempfile.mkdtemp(prefix="blind-eval-home."))
    mkdirs(runtime_home, ".codex", ".claude", ".cargo")
    settings: Path | None = None
    if args.provider == "claude":
        settings = runtime_home / "eval-settings.json"
        claude_settings(settings)
    events = run_dir / "events.jsonl"
    stderr = run_dir / "stderr.log"
    prompt = audit_prompt(
        args.provider,
        manifest["target"],
        manifest.get("repository_label", Path(manifest["repo_root"]).name),
        manifest["reviewer"],
    )
    executable = shutil.which(args.provider)
    if not executable:
        raise EvalError(f"provider CLI is unavailable: {args.provider}")
    version_result = run_checked([executable, "--version"])
    provider_version = version_result.stdout.strip() or version_result.stderr.strip()
    command = minimal_bwrap(case_dir / "fixture", runtime_home, args.provider, settings)
    command += provider_command(args, prompt, settings)

    started = utc_now()
    returncode: int | None = None
    timed_out = False
    try:
        with events.open("w", encoding="utf-8") as out, stderr.open("w", encoding="utf-8") as err:
            try:
                result = subprocess.run(
                    command,
                    stdout=out,
                    stderr=err,
                    text=True,
                    timeout=args.timeout_seconds,
                    check=False,
                )
                returncode = result.returncode
            except subprocess.TimeoutExpired:
                timed_out = True
    finally:
        shutil.rmtree(runtime_home, ignore_errors=True)

    contamination = inspect_contamination(
        events, args.provider, manifest.get("forbidden_repository_markers", [])
    )
    final = extract_final(events, args.provider)
    (run_dir / "final.md").write_text(final.rstrip() + "\n", encoding="utf-8")
    event_count = sum(1 for _ in events.open(encoding="utf-8", errors="replace"))
    metadata = {
        "version": 3,
        "case_id": manifest["case_id"],
        "provider": args.provider,
        "model": args.model,
        "effort": args.effort,
        "provider_version": provider_version,
        "reviewer": manifest["reviewer"],
        "selected_example": manifest["selected_example"],
        "source_commit": manifest["source_commit"],
        "injected_skill_names": manifest["injected_skill_names"],
        "started_at": started,
        "finished_at": utc_now(),
        "returncode": returncode,
        "timed_out": timed_out,
        "contaminated": bool(contamination),
        "contamination": contamination,
        "fixture_verification": "passed",
        "final_message_present": bool(final.strip()),
        "trace_capture": {
            "raw_events": True,
            "reasoning_events_requested": True,
            "partial_messages_requested": args.provider == "claude",
            "subagent_text_requested": args.provider == "claude",
            "provider_may_withhold_private_reasoning": True,
            "events_bytes": events.stat().st_size,
            "events_count": event_count,
        },
    }
    write_json(run_dir / "run.json", metadata)
    print(
        json.dumps(
            {
                "run_dir": str(run_dir),
                "final": str(run_dir / "final.md"),
                "events": str(events),
                "metadata": str(run_dir / "run.json"),
                "returncode": returncode,
                "timed_out": timed_out,
                "contaminated": bool(contamination),
                "fixture_retained": (case_dir / "fixture").is_dir(),
            },
            indent=2,
        )
    )
    if timed_out or returncode != 0 or not final.strip():
        return 2
    return 3 if contamination else 0


def completed_run(case_dir: Path) -> tuple[Path, dict[str, Any]]:
    runs_dir = case_dir / "runs"
    paths = sorted(runs_dir.glob("*/run.json")) if runs_dir.is_dir() else []
    if len(paths) != 1:
        raise EvalError(f"expected exactly one completed run metadata file, found {len(paths)}")
    return paths[0], json.loads(paths[0].read_text(encoding="utf-8"))


def grade(args: argparse.Namespace) -> int:
    case_dir = args.case_dir.resolve()
    manifest = load_manifest(case_dir)
    run_path, run = completed_run(case_dir)
    invalid_reasons = []
    if run.get("returncode") != 0:
        invalid_reasons.append(f"provider return code {run.get('returncode')!r}")
    if run.get("timed_out", False):
        invalid_reasons.append("timeout")
    if run.get("contaminated", False) or run.get("contamination"):
        invalid_reasons.append("contamination")
    if not run.get("final_message_present", False):
        invalid_reasons.append("missing final message")
    if invalid_reasons and args.outcome != "unscored":
        raise EvalError(
            "invalid runs may only be graded unscored: " + ", ".join(invalid_reasons)
        )
    grade_path = case_dir / "grade.json"
    if grade_path.exists() and not args.replace:
        raise EvalError("grade already exists; pass --replace to update it")
    record = {
        "version": 1,
        "case_id": manifest["case_id"],
        "run_metadata": str(run_path.relative_to(case_dir)),
        "run_schema_version": run.get("version", 1),
        "graded_at": utc_now(),
        "outcome": args.outcome,
        "notes": args.notes,
        "invalid_reasons": invalid_reasons,
    }
    write_json(grade_path, record)
    print(json.dumps({"case_dir": str(case_dir), "grade": str(grade_path), **record}, indent=2))
    return 0


def cleanup(args: argparse.Namespace) -> int:
    case_dir = args.case_dir.resolve()
    manifest = load_manifest(case_dir)
    run_path, run = completed_run(case_dir)
    grade_path = case_dir / "grade.json"
    refusal_reasons: list[str] = []
    if not grade_path.is_file():
        refusal_reasons.append("no recorded grade")
    else:
        try:
            recorded_grade = json.loads(grade_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError) as error:
            refusal_reasons.append(f"grade metadata is unreadable: {error}")
        else:
            if recorded_grade.get("case_id") != manifest.get("case_id"):
                refusal_reasons.append("grade belongs to a different case")
            if recorded_grade.get("run_metadata") != str(run_path.relative_to(case_dir)):
                refusal_reasons.append("grade belongs to a different run")
            if recorded_grade.get("outcome") not in {"catch", "partial", "miss", "unscored"}:
                refusal_reasons.append("grade has an invalid outcome")
    if run.get("returncode") != 0:
        refusal_reasons.append(f"provider return code {run.get('returncode')!r}")
    if run.get("timed_out", False):
        refusal_reasons.append("run timed out")
    if run.get("contaminated", False) or run.get("contamination"):
        refusal_reasons.append("run is contaminated")
    if not run.get("final_message_present", False):
        refusal_reasons.append("run has no final message")
    snapshot = case_dir / "injected-skills"
    if not snapshot.is_dir():
        refusal_reasons.append("injected skills snapshot is unavailable")
    else:
        expected_digest = manifest.get("injected_skills_sha256")
        if not isinstance(expected_digest, str) or tree_digest(snapshot) != expected_digest:
            refusal_reasons.append("injected skills snapshot digest mismatch")
    if refusal_reasons and not args.force:
        raise EvalError(
            "refusing cleanup; preserve the fixture for investigation or pass --force: "
            + ", ".join(refusal_reasons)
        )
    fixture = case_dir / "fixture"
    removed = fixture.is_dir()
    if removed:
        shutil.rmtree(fixture)
    print(
        json.dumps(
            {
                "case_dir": str(case_dir),
                "fixture_removed": removed,
                "grade_retained": grade_path.is_file(),
                "forced": args.force,
                "preserved_injected_skills": (case_dir / "injected-skills").is_dir(),
            },
            indent=2,
        )
    )
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(description=__doc__)
    subparsers = root.add_subparsers(dest="command", required=True)

    prepare_parser = subparsers.add_parser(
        "prepare", help="create a sanitized verifier fixture from one historical example"
    )
    prepare_parser.add_argument("--repo", type=Path, default=Path.cwd())
    prepare_parser.add_argument("--example", required=True)
    prepare_parser.add_argument(
        "--reviewer",
        choices=["monolith", "coordinator"],
        required=True,
        help="inject the historical monolith or the coordinator and all specialists",
    )
    prepare_parser.add_argument("--case-id")
    prepare_parser.add_argument("--corpus-skill", type=Path)
    prepare_parser.add_argument("--skills-root", type=Path)
    prepare_parser.add_argument("--output-root", type=Path)
    prepare_parser.set_defaults(func=prepare)

    verify_parser = subparsers.add_parser("verify", help="verify an existing fixture")
    verify_parser.add_argument("--case-dir", type=Path, required=True)
    verify_parser.set_defaults(func=verify)

    run_parser = subparsers.add_parser("run", help="launch a fresh evaluator in the fixture")
    run_parser.add_argument("--case-dir", type=Path, required=True)
    run_parser.add_argument("--provider", choices=["codex", "claude"], required=True)
    run_parser.add_argument("--model")
    run_parser.add_argument("--effort")
    run_parser.add_argument("--timeout-seconds", type=int, default=14400)
    run_parser.set_defaults(func=run_eval)

    grade_parser = subparsers.add_parser(
        "grade", help="record the orchestrator's hidden-answer grading outcome"
    )
    grade_parser.add_argument("--case-dir", type=Path, required=True)
    grade_parser.add_argument(
        "--outcome", choices=["catch", "partial", "miss", "unscored"], required=True
    )
    grade_parser.add_argument("--notes", default="")
    grade_parser.add_argument("--replace", action="store_true")
    grade_parser.set_defaults(func=grade)

    cleanup_parser = subparsers.add_parser(
        "cleanup", help="remove a graded case fixture while retaining all run artifacts"
    )
    cleanup_parser.add_argument("--case-dir", type=Path, required=True)
    cleanup_parser.add_argument(
        "--force",
        action="store_true",
        help="allow cleanup of ungraded, failed, contaminated, or incomplete runs",
    )
    cleanup_parser.set_defaults(func=cleanup)
    return root


def main() -> int:
    try:
        args = parser().parse_args()
        return args.func(args)
    except EvalError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
