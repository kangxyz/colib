#!/usr/bin/env python3
"""Validate and export the structured Colib Library from its editorial owners and Lean tags."""

import argparse
import hashlib
from html import escape
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib
from urllib.parse import quote, urlsplit

import library_text

ROOT = Path(__file__).resolve().parents[1]
RELATIONS = {
    "whole",
    "clause",
    "generalization",
    "specialization",
    "adaptation",
    "comparison",
    "ingredient",
    "background",
    "source_tag",
}
KINDS = {
    "definition",
    "lemma",
    "proposition",
    "theorem",
    "corollary",
    "example",
    "comparison",
}
SLUG = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*")
STACKS_TAG = re.compile(r"Tag ([A-Z0-9]{4})(?:\([0-9]+\))?")
GITHUB_TREE = re.compile(r"https://github\.com/([^/?#]+/[^/?#]+)/tree/([0-9a-f]{40})")
LEAN_FILE = re.compile(r"([A-Za-z0-9_][A-Za-z0-9_./-]*\.lean)(?=[:,; ]|$)")
LINE_RANGES = re.compile(r"(?::\s*|,\s*lines?\s+)(\d+(?:[-–]\d+)?(?:,\s*\d+(?:[-–]\d+)?)*)")
LINE_PREFIX = re.compile(r":\s*\d|,\s*lines?\b")
LIBRARY_URL = "https://kangxyz.github.io/colib/"


def check_url(url):
    parsed = urlsplit(url)
    if (
        parsed.scheme != "https" or not parsed.hostname
        or parsed.username or parsed.password or any(char.isspace() for char in url)
    ):
        raise ValueError(f"Expected an HTTPS source link, got {url!r}")


def check_prose(text, library, label):
    try:
        for kind, value in library_text.tokens(text):
            if kind == "item" and value not in library["entries"] and value not in library["retired"]:
                raise ValueError(f"Unknown Library item {value}")
            if kind == "citation":
                key, locator = library_text.citation_parts(value)
                if key not in library["sources"]:
                    raise ValueError(f"Unknown bibliography key {key}")
                if key == "stacks" and locator and not STACKS_TAG.fullmatch(locator):
                    raise ValueError("Use Tag XXXX for a Stacks Project locator")
                if locator:
                    reference_locations(key, library["sources"][key], locator)
    except ValueError as error:
        raise ValueError(f"{label}: {error}") from error


def load_library(root=ROOT):
    with (root / "docs/references.toml").open("rb") as stream:
        sources = tomllib.load(stream)["sources"]
    for key, source in sources.items():
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", key):
            raise ValueError(f"Unsafe bibliographic key {key}")
        for field in ("kind", "title", "authors", "version", "url"):
            if not source.get(field):
                raise ValueError(f"Source {key} needs {field}")
        check_url(source["url"])
        roots = source.get("locator_roots", [])
        if not isinstance(roots, list) or any(not re.fullmatch(r"[A-Za-z0-9_]+", root) for root in roots):
            raise ValueError(f"Source {key} needs valid repository locator roots")
        for document in source.get("documents", []):
            if not re.fullmatch(r"[0-9a-f]{64}", document.get("sha256", "")):
                raise ValueError(f"Source {key} needs an exact document hash")
            check_url(document["url"])
    chapters, sections, entries = [], {}, {}
    for path in sorted((root / "docs/library/chapters").glob("*.toml")):
        data = tomllib.loads(path.read_text())
        chapter = data["chapter"]
        if not SLUG.fullmatch(chapter["id"]) or any(
            c["id"] == chapter["id"] for c in chapters
        ):
            raise ValueError(f"Invalid or duplicate chapter {chapter['id']}")
        if type(chapter.get("order")) is not int or chapter["order"] < 0:
            raise ValueError(
                f"Chapter {chapter['id']} needs a nonnegative integer order"
            )
        for field in ("title", "introduction"):
            if not chapter.get(field):
                raise ValueError(f"Chapter {chapter['id']} needs {field}")
        chapter["sections"] = []
        for section in data["sections"]:
            identifier = section["id"]
            if not SLUG.fullmatch(identifier) or identifier in sections:
                raise ValueError(f"Invalid or duplicate section {identifier}")
            if type(section.get("order")) is not int or section["order"] < 0:
                raise ValueError(
                    f"Section {identifier} needs a nonnegative integer order"
                )
            if "modules" in section:
                raise ValueError("Module ownership is exported from Lean")
            if not section.get("introduction"):
                raise ValueError(f"Section {identifier} needs an introduction")
            section = dict(section, chapter=chapter["id"], entries=[])
            sections[identifier] = section
            chapter["sections"].append(identifier)
        chapter["sections"].sort(
            key=lambda identifier: (sections[identifier]["order"], identifier)
        )
        chapters.append(chapter)
    for path in sorted((root / "docs/library/entries").rglob("*.toml")):
        entry = tomllib.loads(path.read_text())["entry"]
        identifier = entry["id"]
        if not re.fullmatch(r"COL-[0-9]{4,}", identifier) or identifier in entries:
            raise ValueError(f"Invalid or duplicate Library ID {identifier}")
        if any(
            field in entry
            for field in ("declarations", "reference", "locator", "requires")
        ):
            raise ValueError(
                f"{identifier} declaration bindings and citations belong in Lean attributes; dependencies come from Lean"
            )
        for field in ("title", "statement", "scope"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                raise ValueError(f"{identifier} needs {field}")
        if type(entry.get("order")) is not int or entry["order"] < 0:
            raise ValueError(f"{identifier} needs a nonnegative integer order")
        if entry["kind"] not in KINDS or entry["section"] not in sections:
            raise ValueError(f"{identifier} has an unknown item kind or section")
        if entry["review"] != "author_checked":
            raise ValueError(
                f"{identifier} needs its supported, explicit review status"
            )
        proof_kind = entry.get("proof_kind", "outline")
        if proof_kind not in ("proof", "outline") or (
            proof_kind == "proof" and not entry.get("proof", "").strip()
        ):
            raise ValueError(f"{identifier} needs a proof or proof outline matching its proof kind")
        if "source_checked_on" in entry and (
            not isinstance(entry["source_checked_on"], str)
            or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", entry["source_checked_on"])
        ):
            raise ValueError(f"{identifier} needs a source check date in YYYY-MM-DD format")
        if entry.get("provenance") and entry["provenance"] not in sources:
            raise ValueError(f"{identifier} has an unknown provenance key")
        entry["path"] = str(path.relative_to(root))
        entries[identifier] = entry
        sections[entry["section"]]["entries"].append(identifier)
    retired = {}
    for path in sorted((root / "docs/library/retired").glob("*.toml")):
        item = tomllib.loads(path.read_text())["retired"]
        identifier = item["id"]
        if (not re.fullmatch(r"COL-[0-9]{4,}", identifier)
                or identifier in entries or identifier in retired):
            raise ValueError(f"Invalid or reused retired Library ID {identifier}")
        for field in ("title", "reason"):
            if not isinstance(item.get(field), str) or not item[field].strip():
                raise ValueError(f"{identifier} needs a retirement {field}")
        if not re.fullmatch(r"[0-9a-f]{40}", item.get("previous_revision", "")):
            raise ValueError(f"{identifier} needs an exact previous revision")
        previous = Path(item.get("previous_path", ""))
        if (previous.is_absolute() or ".." in previous.parts
                or not str(previous).startswith("docs/library/entries/")
                or previous.name != identifier + ".toml"):
            raise ValueError(f"{identifier} needs its previous Library path")
        if any(value not in entries for value in item.get("related_items", [])):
            raise ValueError(f"{identifier} has an unknown related Library item")
        retired[identifier] = dict(item, status="retired", path=str(path.relative_to(root)))
    if not entries or not chapters:
        raise ValueError("The Library needs occupied mathematical chapters and items")
    for section in sections.values():
        if not section["entries"]:
            raise ValueError(f"Section {section['id']} has no mathematical items")
        section["entries"].sort(
            key=lambda identifier: (entries[identifier]["order"], identifier)
        )
        if topics := section.get("topics"):
            positions = {identifier: i for i, identifier in enumerate(section["entries"])}
            starts = []
            slugs = set()
            for topic in topics:
                slug = topic["id"]
                if not SLUG.fullmatch(slug) or slug in slugs or not topic.get("title"):
                    raise ValueError(f"Invalid topic in section {section['id']}")
                if topic["start"] not in positions:
                    raise ValueError(f"Topic {slug} must start at an item of {section['id']}")
                slugs.add(slug)
                starts.append(positions[topic["start"]])
            if starts[0] != 0 or starts != sorted(set(starts)):
                raise ValueError(f"Topics must partition the reading order of {section['id']}")
            for topic, start, end in zip(topics, starts, starts[1:] + [len(positions)]):
                topic["entries"] = section["entries"][start:end]
    chapters.sort(key=lambda chapter: (chapter["order"], chapter["id"]))
    library = {
        "sources": sources,
        "chapters": chapters,
        "sections": sections,
        "entries": entries,
        "retired": retired,
    }
    for section in sections.values():
        legacy_items = section.get("legacy_items", [])
        if (not isinstance(legacy_items, list) or
                any(not isinstance(identifier, str) for identifier in legacy_items) or
                len(legacy_items) != len(set(legacy_items))):
            raise ValueError(f"Section {section['id']} needs distinct legacy item IDs")
        for identifier in legacy_items:
            if identifier not in entries or identifier in section["entries"]:
                raise ValueError(f"Section {section['id']} has an invalid moved item {identifier}")
        transitions = section.get("transitions", {})
        if not isinstance(transitions, dict):
            raise ValueError(f"Section {section['id']} transitions must be a table")
        for identifier, text in transitions.items():
            label = f"Section {section['id']} transition before {identifier}"
            if identifier not in section["entries"]:
                raise ValueError(f"{label} must precede an item of the same section")
            if not isinstance(text, str) or not text.strip():
                raise ValueError(f"{label} needs prose")
            check_prose(text, library, label)
    for records, fields in (
        (chapters, ("title", "introduction")),
        (sections.values(), ("title", "introduction")),
        (entries.values(), ("title", "statement", "scope", "proof")),
        (retired.values(), ("title", "reason")),
        ((topic for section in sections.values() for topic in section.get("topics", [])), ("title",)),
    ):
        for record in records:
            for field in fields:
                if value := record.get(field):
                    check_prose(value, library, f"{record['id']} {field}")
    return library


def load_catalog(root=ROOT):
    """Retain the original metadata-reading API for existing tools."""
    library = load_library(root)
    return library["sources"], list(library["entries"].values())


def check_sources(root=ROOT):
    roots = {"Colib", "Mathlib", "StacksCore", "StacksFrontier"}
    for path in sorted((root / "Colib").rglob("*.lean")):
        tokens = re.split(r"(/-|-/|--|\n)", path.read_text())
        depth, line_comment, code = 0, False, []
        for token in tokens:
            if line_comment:
                if token == "\n":
                    line_comment = False
                    code.append(token)
                continue
            if token == "/-":
                depth += 1
            elif token == "-/":
                if depth == 0:
                    raise ValueError(f"Unbalanced comments in {path}")
                depth -= 1
            elif depth == 0:
                if token == "--":
                    line_comment = True
                else:
                    code.append(token)
        if depth != 0:
            raise ValueError(f"Unbalanced comments in {path}")
        text = "".join(code)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", text):
            raise ValueError(f"Production placeholder or added axiom in {path}")
        for name in re.findall(
            r"(?m)^(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(\S+)", text
        ):
            if name.split(".")[0] not in roots:
                raise ValueError(
                    f"Production import outside the dependency boundary in {path}"
                )


def source_link(module, pins, revision):
    relative = module.replace(".", "/") + ".lean"
    provider = module.split(".")[0]
    if provider == "Colib":
        return f"https://github.com/kangxyz/colib/blob/{revision}/{relative}"
    if provider not in {"Mathlib", "StacksCore", "StacksFrontier"}:
        raise ValueError(f"Unsupported catalog source provider {provider}")
    package = "mathlib" if provider == "Mathlib" else "Stacks"
    pin = pins[package]
    return f"{pin['url'].removesuffix('.git')}/blob/{pin['rev']}/{relative}"


def reference_locations(key, source, locator):
    """Resolve the recorded locator against its own source and pinned version."""
    url = source["url"]
    if key == "stacks" and (tag := STACKS_TAG.fullmatch(locator)):
        return [{"label": locator, "url": f"{url.rstrip('/')}/tag/{tag[1]}"}]
    if source["kind"] == "software" and (tree := GITHUB_TREE.fullmatch(url)) and (file := LEAN_FILE.match(locator)):
        path = file[1]
        if any(part in ("", ".", "..") for part in path.split("/")):
            raise ValueError(f"Invalid repository path in {locator!r}")
        roots = source.get("locator_roots", [])
        if roots and path.split("/", 1)[0] not in roots:
            path = f"{roots[0]}/{path}"
        url = f"https://github.com/{tree[1]}/blob/{tree[2]}/{quote(path)}"
        suffix = locator[file.end():]
        if lines := LINE_RANGES.fullmatch(suffix):
            ranges = [line.strip() for line in lines[1].split(",")]
            locations = []
            for index, line in enumerate(ranges):
                first, _, last = line.replace("–", "-").partition("-")
                if int(first) < 1 or (last and int(last) < int(first)):
                    raise ValueError(f"Invalid line range in {locator!r}")
                anchor = f"L{first}" + (f"-L{last}" if last else "")
                if len(ranges) == 1:
                    label = locator
                else:
                    label = f"{file[1]}:{line}" if index == 0 else f"Lines {line}"
                locations.append({"label": label, "url": f"{url}#{anchor}"})
            return locations
        if LINE_PREFIX.match(suffix):
            raise ValueError(f"Invalid line range in {locator!r}")
        return [{"label": locator, "url": url}]
    documents = [
        document for document in source.get("documents", [])
        if document.get("locator_prefix") and locator.startswith(document["locator_prefix"])
    ]
    if documents:
        url = max(documents, key=lambda document: len(document["locator_prefix"]))["url"]
    return [{"label": locator, "url": url}]


def prose_citation_links(library, value, root):
    key, locator = library_text.citation_parts(value)
    source = library["sources"][key]
    if not locator:
        return [{"label": source["title"], "url": root + "references/" + key + "/"}]
    locations = reference_locations(key, source, locator)
    if key != "stacks":
        short_title = source.get("short_title", source["title"])
        locations[0]["label"] = f'{short_title}, {locations[0]["label"]}'
    return locations


def compile_library(library, native, pins, revision):
    entries = {
        identifier: dict(
            entry, declarations=[], references=[], used_by=[], formal_dependencies=[]
        )
        for identifier, entry in library["entries"].items()
    }
    declarations = {row["name"]: dict(row) for row in native["declarations"]}
    memberships = {}
    for binding in native["bindings"]:
        identifier, name = binding["id"], binding["name"]
        if identifier not in entries or name not in declarations:
            raise ValueError(f"Unknown compiled Library binding {identifier} / {name}")
        if name not in entries[identifier]["declarations"]:
            entries[identifier]["declarations"].append(name)
        memberships.setdefault(name, set()).add(identifier)
    for entry in entries.values():
        if not entry["declarations"]:
            raise ValueError(
                f"{entry['id']} needs a compiled @[colib_tag] declaration binding"
            )
        if primary := entry.get("primary"):
            if primary not in entry["declarations"]:
                raise ValueError(f"{entry['id']} primary declaration needs a compiled binding")
            entry["declarations"].remove(primary)
            entry["declarations"].insert(0, primary)
    citations = list(native["citations"])
    citations.extend(
        {
            "name": row["name"],
            "source": "stacks",
            "locator": "Tag " + row["tag"],
            "relation": "source_tag",
            "scope": row["scope"],
        }
        for row in native["stacks"]
    )
    resolved_citations = []
    for citation in citations:
        if citation["name"] not in declarations:
            raise ValueError("A native citation needs its declaring Lean constant")
        key = citation["source"]
        if key not in library["sources"]:
            raise ValueError(f"Unknown bibliographic key {key} on {citation['name']}")
        if not citation["locator"].strip() or citation["relation"] not in RELATIONS:
            raise ValueError(
                f"Invalid literature locator or relation on {citation['name']}"
            )
        if citation["relation"] == "source_tag" and not STACKS_TAG.fullmatch(citation["locator"]):
            raise ValueError(f"Invalid Stacks tag on {citation['name']}")
        citation = dict(citation)
        check_prose(citation["scope"], library, f"{citation['name']} citation scope")
        if "url" in citation:
            check_url(citation["url"])
            locations = [{"label": citation["locator"], "url": citation["url"]}]
        else:
            locations = reference_locations(key, library["sources"][key], citation["locator"])
        citation["url"] = locations[0]["url"]
        citation["locations"] = locations
        resolved_citations.append(citation)
        for identifier in memberships.get(citation["name"], set()):
            entries[identifier]["references"].append(citation)
    for name, declaration in declarations.items():
        declaration["source_url"] = source_link(declaration["module"], pins, revision)
        targets = {
            identifier
            for dependency in declaration.get("dependencies", [])
            for identifier in memberships.get(dependency, set())
        }
        for identifier in memberships.get(name, set()):
            entries[identifier]["formal_dependencies"].extend(targets - {identifier})
    for entry in entries.values():
        if not entry["references"]:
            raise ValueError(f"{entry['id']} needs a compiled precise source reference")
        entry["formal_dependencies"] = sorted(set(entry["formal_dependencies"]))
    for entry in entries.values():
        for dependency in entry["formal_dependencies"]:
            entries[dependency]["used_by"].append(entry["id"])
    sections = {key: dict(value) for key, value in library["sections"].items()}
    for section in sections.values():
        section["modules"] = sorted(
            {
                declarations[name]["module"]
                for identifier in section["entries"]
                for name in entries[identifier]["declarations"]
            }
        )
    modules = {
        row["name"]: dict(row, source_url=source_link(row["name"], pins, revision))
        for row in native["modules"]
    }
    return dict(
        library,
        schema=2,
        revision=revision,
        sections=sections,
        entries=entries,
        declarations=declarations,
        modules=modules,
        citations=resolved_citations,
    )


def source_hashes(root=ROOT):
    paths = [
        root / "Colib.lean",
        root / "lakefile.toml",
        root / "lake-manifest.json",
        root / "lean-toolchain",
    ]
    paths.extend((root / "Colib").rglob("*.lean"))
    return {
        str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(paths)
    }


def markdown_link(label, url):
    label = escape(label).replace("[", r"\[").replace("]", r"\]")
    return f"[{label}](<{url}>)"


def markdown_prose(text, library):
    parts = []
    for kind, value in library_text.tokens(text):
        if kind == "math":
            parts.append(f"${value}$")
        elif kind == "display":
            parts.append(f"\n\n$$\n{value}\n$$\n\n")
        elif kind == "code":
            parts.append("`" + value + "`")
        elif kind == "item":
            parts.append(markdown_link(value, LIBRARY_URL + "tag/" + value + "/"))
        elif kind == "citation":
            parts.append(" · ".join(
                markdown_link(link["label"], link["url"])
                for link in prose_citation_links(library, value, LIBRARY_URL)
            ))
        else:
            parts.append(escape(value, quote=False))
    return "".join(parts)


def render_markdown(library):
    lines = ["# Colib Library", "", f"Source revision `{library['revision']}`.", ""]
    for chapter in library["chapters"]:
        lines.extend([
            "## " + markdown_prose(chapter["title"], library), "",
            markdown_prose(chapter["introduction"], library), "",
        ])
        for section_id in chapter["sections"]:
            section = library["sections"][section_id]
            lines.extend([
                "### " + markdown_prose(section["title"], library), "",
                markdown_prose(section["introduction"], library), "",
            ])
            transitions = section.get("transitions", {})
            topic_titles = {topic["start"]: topic["title"] for topic in section.get("topics", [])}
            item_heading = "#####" if topic_titles else "####"
            for identifier in section["entries"]:
                entry = library["entries"][identifier]
                if title := topic_titles.get(identifier):
                    lines.extend(["#### " + markdown_prose(title, library), ""])
                if text := transitions.get(identifier):
                    lines.extend([markdown_prose(text, library), ""])
                lines.extend(
                    [
                        f'<a id="{identifier}"></a>',
                        "",
                        f"{item_heading} {identifier} — {entry['kind'].title()}. "
                        + markdown_prose(entry["title"], library),
                        "",
                        markdown_prose(entry["statement"], library),
                        "",
                        markdown_prose(entry["scope"], library),
                        "",
                        "Direct Lean references — "
                        + (", ".join(
                            markdown_link(item, LIBRARY_URL + "tag/" + item + "/")
                            for item in entry["formal_dependencies"]
                        ) or "None"),
                        "",
                    ]
                )
                if entry.get("proof"):
                    label = "Proof." if entry.get("proof_kind") == "proof" else "Proof outline."
                    lines.extend([label, "", markdown_prose(entry["proof"], library), ""])
                seen = set()
                for citation in entry["references"]:
                    key = citation["source"]
                    identity = (key, citation["locator"], citation["url"], citation["relation"], citation["scope"])
                    if identity in seen:
                        continue
                    seen.add(identity)
                    source = library["sources"][key]
                    locations = citation.get("locations", [{"label": citation["locator"], "url": citation["url"]}])
                    relation = "Stacks tag" if citation["relation"] == "source_tag" else citation["relation"].capitalize()
                    lines.append(
                        "- " + markdown_link(source["title"], LIBRARY_URL + "references/" + key + "/")
                        + " · " + " · ".join(markdown_link(link["label"], link["url"]) for link in locations)
                        + " · " + relation
                        + (" · " + markdown_prose(citation["scope"], library) if citation["scope"] else "")
                    )
                lines.append("")
                for name in entry["declarations"]:
                    declaration = library["declarations"][name]
                    lines.extend(
                        [
                            f"[`{name}`]({declaration['source_url']})",
                            "",
                            "```lean",
                            "import " + declaration["module"],
                            "#check " + name,
                            "```",
                            "",
                            "```lean",
                            declaration["type"],
                            "```",
                            "",
                        ]
                    )
    return "\n".join(lines)


def build_catalog(root=ROOT):
    editorial = load_library(root)
    check_sources(root)
    result = subprocess.run(
        ["lake", "env", "lean", "scripts/export_catalog.lean"],
        cwd=root,
        check=True,
        text=True,
        capture_output=True,
    )
    native = json.loads(result.stdout)
    pins = {
        row["name"]: row
        for row in json.loads((root / "lake-manifest.json").read_text())["packages"]
    }
    observed = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    revision = os.environ.get("GITHUB_SHA", observed.stdout.strip() or "main")
    library = compile_library(editorial, native, pins, revision)
    library["compiler"] = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=root, text=True
    ).strip()
    library["source_hashes"] = source_hashes(root)
    output = root / "build/library"
    output.mkdir(parents=True, exist_ok=True)
    (output / "index.md").write_text(render_markdown(library))
    (output / "library.json").write_text(
        json.dumps(library, ensure_ascii=False, indent=2) + "\n"
    )
    (output / "declarations.json").write_text(
        json.dumps(
            dict(
                native,
                revision=revision,
                compiler=library["compiler"],
                source_hashes=library["source_hashes"],
            ),
            ensure_ascii=False,
            indent=2,
        )
        + "\n"
    )
    # Preserve the original generated-output paths for existing release consumers.
    legacy = root / "build/catalog"
    legacy.mkdir(parents=True, exist_ok=True)
    for filename in ("index.md", "declarations.json"):
        shutil.copyfile(output / filename, legacy / filename)
    print(
        f"Exported {len(library['entries'])} Library items and {len(library['declarations'])} indexed declarations"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "build", "show"))
    parser.add_argument("identifier", nargs="?")
    args = parser.parse_args()
    if args.command == "build":
        build_catalog()
    elif args.command == "show":
        library = load_library()
        if args.identifier in library["retired"]:
            print(json.dumps(library["retired"][args.identifier], ensure_ascii=False, indent=2))
            return
        if args.identifier not in library["entries"]:
            raise ValueError("Select an existing permanent Library ID")
        entry = library["entries"][args.identifier]
        section = library["sections"][entry["section"]]
        data = dict(entry, chapter=section["chapter"])
        export = ROOT / "build/library/library.json"
        if export.exists():
            built = json.loads(export.read_text())
            if built.get("source_hashes") == source_hashes():
                data["declarations"] = built["entries"][args.identifier]["declarations"]
                data["modules"] = sorted(
                    {
                        built["declarations"][name]["module"]
                        for name in data["declarations"]
                    }
                )
        print(json.dumps(data, ensure_ascii=False, indent=2))
    else:
        library = load_library()
        check_sources()
        print(
            f"Checked {len(library['chapters'])} chapters, {len(library['sections'])} sections and "
            f"{len(library['entries'])} permanent items"
        )


if __name__ == "__main__":
    try:
        main()
    except (
        ValueError,
        KeyError,
        tomllib.TOMLDecodeError,
        subprocess.CalledProcessError,
    ) as error:
        if isinstance(error, subprocess.CalledProcessError):
            for output in (error.stdout, error.stderr):
                if output:
                    print(output, file=sys.stderr)
        print(f"Library error — {error}", file=sys.stderr)
        sys.exit(1)
