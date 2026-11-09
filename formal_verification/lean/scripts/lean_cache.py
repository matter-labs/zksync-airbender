#!/usr/bin/env python3
"""Choose small Lean build snapshots and retain their exact branch replacement.

These are mutable build hints, never proof or replay qualification. Cache
maintenance is best effort and cannot change a verification result.
"""
import argparse
import json
import os
import re
from urllib.parse import urlencode
from urllib.request import Request, urlopen


COMPLETE_KEY = re.compile(r"fv-lean-v3-(?:Linux|macOS|Windows)-[A-Za-z0-9_]+-"
                          r"[0-9a-f]{64}-[0-9a-f]{64}-complete")
PROGRESS_KEY = re.compile(r"fv-lean-v3-(?:Linux|macOS|Windows)-[A-Za-z0-9_]+-"
                          r"[0-9a-f]{64}-[0-9a-f]{64}-[0-9]+-[0-9]+-progress")


def snapshot_key(complete, progress, source, bootstrap, exact_hit):
    """A passing complete source/runtime/Review stage is a completed build.

    Later decoder/audit/replay failures do not need another copy of this same
    content. Failed source/bootstrap attempts can still retain useful progress.
    """
    if not COMPLETE_KEY.fullmatch(complete) or not PROGRESS_KEY.fullmatch(progress):
        raise ValueError("invalid Lean snapshot key")
    if re.sub(r"-[0-9]+-[0-9]+-progress$", "-complete", progress) != complete:
        raise ValueError("Lean snapshot content identities differ")
    if exact_hit == "true":
        return ""
    if source == "success":
        return complete
    if source in ("failure", "cancelled") or bootstrap in ("success", "failure", "cancelled"):
        return progress
    return ""


class GitHub:
    def __init__(self, repository, token, api_url="https://api.github.com"):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise ValueError("invalid repository")
        self.base = api_url.rstrip("/") + "/repos/" + repository
        self.token = token

    def request(self, method, path):
        request = Request(self.base + path, method=method, headers={
            "Accept": "application/vnd.github+json",
            "Authorization": "Bearer " + self.token,
            "X-GitHub-Api-Version": "2022-11-28",
        })
        with urlopen(request, timeout=30) as response:
            body = response.read()
        return json.loads(body) if body else None

    def caches(self, ref):
        result = []
        page = 1
        while True:
            query = urlencode({"ref": ref, "key": "fv-lean-", "per_page": 100,
                               "page": page})
            rows = self.request("GET", "/actions/caches?" + query)["actions_caches"]
            result.extend(rows)
            if len(rows) < 100:
                return result
            page += 1

    def delete(self, cache_id):
        self.request("DELETE", "/actions/caches/" + str(cache_id))


def prune(api, ref, keep_key):
    """Delete only older FV Lean snapshots after observing the replacement.

    Cache-action success alone is insufficient: failed/missing publication and
    read-only tokens must preserve all useful snapshots. A complete listing is
    obtained before any deletion, and newer concurrent entries are retained.
    """
    if not ref.startswith("refs/heads/") or not ref.removeprefix("refs/heads/"):
        raise ValueError("Lean cache retention requires an exact branch ref")
    if not (COMPLETE_KEY.fullmatch(keep_key) or PROGRESS_KEY.fullmatch(keep_key)):
        raise ValueError("invalid replacement Lean cache key")
    rows = api.caches(ref)
    matches = [row for row in rows if row["ref"] == ref and row["key"] == keep_key
               and row["size_in_bytes"] > 0]
    if not matches:
        return {"status": "not-published", "deleted": []}
    keep = max(matches, key=lambda row: row["created_at"])
    # Confirm it is still present immediately before starting destructive work.
    current = next((row for row in api.caches(ref) if row["id"] == keep["id"]), None)
    if current is None or any(current[field] != keep[field] for field in
                              ("ref", "key", "created_at", "size_in_bytes")):
        return {"status": "replacement-disappeared", "deleted": []}
    deleted = []
    for row in rows:
        if (row["ref"] == ref and row["id"] != keep["id"]
                and row["key"].startswith(("fv-lean-v2-", "fv-lean-v3-"))
                and row["created_at"] < keep["created_at"]):
            api.delete(row["id"])
            deleted.append(row["id"])
    return {"status": "retained", "id": keep["id"], "key": keep_key,
            "size_in_bytes": keep["size_in_bytes"], "deleted": deleted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("plan", "prune"))
    args = parser.parse_args()
    if args.command == "plan":
        key = snapshot_key(os.environ["FV_LEAN_COMPLETE_KEY"],
                           os.environ["FV_LEAN_PROGRESS_KEY"],
                           os.environ["FV_LEAN_SOURCE_OUTCOME"],
                           os.environ["FV_LEAN_BOOTSTRAP_OUTCOME"],
                           os.environ.get("FV_LEAN_EXACT_HIT", ""))
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            output.write("key=" + key + "\n")
        print(json.dumps({"snapshot_key": key or None}))
        return
    try:
        api = GitHub(os.environ["GITHUB_REPOSITORY"], os.environ["GH_TOKEN"],
                     os.environ.get("GITHUB_API_URL", "https://api.github.com"))
        report = prune(api, os.environ["GITHUB_REF"], os.environ["FV_LEAN_KEEP_KEY"])
    except Exception as error:
        # Maintenance can lack Actions write permission or fail independently
        # of the proof job. Never print credentials or reinterpret verification.
        report = {"status": "maintenance-unavailable", "error": type(error).__name__}
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
