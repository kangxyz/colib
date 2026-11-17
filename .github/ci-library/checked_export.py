"""Select a declaration export from successful Colib CI on main."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryFile
from zipfile import ZipFile


NATIVE_INPUTS = (
    "Colib", "ColibTest", ":(glob)**/*.lean", ".lake", "lakefile.toml",
    "lake-manifest.json", "lean-toolchain",
)


def api(path, *options):
    return json.loads(subprocess.check_output(["gh", "api", path, *options]))


def git_matches(*args):
    result = subprocess.run(["git", *args])
    if result.returncode not in (0, 1):
        result.check_returncode()
    return result.returncode == 0


def select_export(repo, revision):
    """Match immutable source inputs, including the Lean exporter."""
    repository = api(repo)
    repository_id = repository["id"]
    pages = api(repo + "/actions/artifacts?name=colib-library&per_page=100", "--paginate", "--slurp")
    for artifact in (item for page in pages for item in page["artifacts"]):
        producer = artifact.get("workflow_run") or {}
        base = producer.get("head_sha", "")
        if (
            artifact["expired"]
            or producer.get("head_branch") != "main"
            or producer.get("repository_id") != repository_id
            or producer.get("head_repository_id") != repository_id
            or not re.fullmatch(r"[0-9a-f]{40}", base)
        ):
            continue
        if subprocess.run(
            ["git", "cat-file", "-e", f"{base}^{{commit}}"], stderr=subprocess.DEVNULL
        ).returncode:
            continue
        if not git_matches("merge-base", "--is-ancestor", base, revision):
            continue
        if not git_matches("diff", "--quiet", "--no-ext-diff", base, revision, "--", *NATIVE_INPUTS):
            continue
        run = api(f"{repo}/actions/runs/{producer['id']}")
        if (
            run["path"] == ".github/workflows/ci.yml"
            and run["event"] in ("push", "workflow_dispatch")
            and run["conclusion"] == "success"
            and run["head_sha"] == base
        ):
            return artifact
    raise ValueError("No compatible declaration export from successful Colib CI on main. Run full CI on main.")


def download(repo, artifact, destination):
    with TemporaryFile() as archive:
        subprocess.run(
            ["gh", "api", f"{repo}/actions/artifacts/{artifact['id']}/zip"], stdout=archive, check=True
        )
        with ZipFile(archive) as bundle:
            data = bundle.read("declarations.json")
    producer = artifact["workflow_run"]
    if json.loads(data).get("revision") != producer["head_sha"]:
        raise ValueError("The checked declaration export revision differs from its CI run")
    destination.write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    if revision != os.environ.get("GITHUB_SHA", revision):
        raise ValueError("The Library checkout differs from the requested revision")
    repo = "repos/" + os.environ["GITHUB_REPOSITORY"]
    artifact = select_export(repo, revision)
    download(repo, artifact, args.destination)
    producer = artifact["workflow_run"]
    message = (
        f"Library revision `{revision}`\n\n"
        f"Checked Lean declarations from `{producer['head_sha']}` (CI run {producer['id']}).\n"
    )
    print(message)
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(summary).open("a") as output:
            output.write(message)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"Library export selection failed — {error}")
