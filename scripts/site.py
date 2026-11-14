#!/usr/bin/env python3
"""Generate chapter, section, item and bibliography pages for the Colib Library."""

import argparse
from html import escape
import json
from pathlib import Path
import re
import shutil
from unicodedata import normalize

import catalog
import lean_code
import library_text


def anchor(text, path):
    return f'<a href="{escape(path, quote=True)}">{escape(text)}</a>'


def build(library_path, output):
    library = json.loads(Path(library_path).read_text())
    if (
        library.get("schema") != 2
        or library.get("source_hashes") != catalog.source_hashes()
    ):
        raise ValueError(
            "Build the Library export for the current Lean source and pins first"
        )
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    chapters = library["chapters"]
    sections = library["sections"]
    entries = library["entries"]
    sources = library["sources"]
    template = (catalog.ROOT / "docs/site/index.html").read_text()
    source_lines = {}

    def prose(text, root, *, links=True, paragraphs=False):
        parts = []
        for kind, value in library_text.tokens(text.strip() if paragraphs else text):
            if kind in ("math", "display"):
                display = kind == "display"
                attrs = ' class="tex-display" data-display="true"' if display else ""
                left, right = (r"\[", r"\]") if display else (r"\(", r"\)")
                parts.append(
                    f'<span data-tex="{escape(value, quote=True)}"{attrs}>'
                    + escape(left + value + right)
                    + "</span>"
                )
            elif kind == "code":
                parts.append(f"<code>{escape(value)}</code>")
            elif kind == "item" and links:
                parts.append(anchor(value, root + "tag/" + value + "/"))
            elif kind == "citation":
                parts.append(" · ".join(
                    anchor(link["label"], link["url"]) if links else escape(link["label"])
                    for link in catalog.prose_citation_links(library, value, root)
                ))
            else:
                value = escape(value)
                if paragraphs and kind == "text":
                    value = re.sub(r"\n(?:[ \t]*\n)+", "</p><p>", value)
                parts.append(value)
        html = "".join(parts)
        return f"<p>{html}</p>" if paragraphs else html

    def prose_link(text, path, root):
        return f'<a href="{escape(path, quote=True)}">{prose(text, root, links=False)}</a>'

    def location_links(citation, root):
        locations = citation.get("locations", [{"label": citation["locator"], "url": citation["url"]}])
        links = []
        for target in locations:
            label = target["label"]
            if file := catalog.LEAN_FILE.match(label):
                path = escape(file[1]).replace("/", "/<wbr>")
                suffix = label[file.end():]
                text = f'<span class="reference-file">{path}</span>'
                if catalog.LINE_RANGES.fullmatch(suffix):
                    text += f'<wbr><span class="reference-lines">{escape(suffix)}</span>'
                else:
                    text += prose(suffix, root, links=False)
                links.append(f'<a href="{escape(target["url"], quote=True)}">{text}</a>')
            else:
                links.append(prose_link(label, target["url"], root))
        return " · ".join(links)

    def render_references(citations, root):
        groups = {}
        for citation in citations:
            identity = (citation["source"], citation["relation"], citation["scope"])
            locators = groups.setdefault(identity, {})
            locators[citation["locator"], citation["url"]] = citation
        rows = []
        for (key, relation, scope), locators in groups.items():
            source = sources[key]
            title = anchor(
                source.get("short_title", source["title"]), root + "references/" + key + "/"
            )
            label = "Stacks tag" if relation == "source_tag" else relation.capitalize()
            rows.append(
                '<li><p class="reference-location">' + title + ", "
                + " · ".join(location_links(citation, root) for citation in locators.values())
                + '</p><p class="reference-scope"><span class="reference-relation">'
                + label + "</span>" + (" · " + prose(scope, root) if scope else "")
                + "</p></li>"
            )
        return '<ul class="reference-list">' + "".join(rows) + "</ul>"

    def render_import(declaration):
        module = escape(declaration["module"]).replace(".", ".<wbr>")
        import_text = "import " + declaration["module"]
        return (
            '<code><span class="lean-keyword">import</span> ' + module
            + '</code><button class="copy" data-copy="' + escape(import_text, quote=True)
            + '" aria-label="Copy import">Copy</button>'
        )

    def render_declaration_identity(declaration):
        name = escape(declaration["name"]).replace(".", ".<wbr>")
        return (
            '<dl class="declaration-identity"><dt>Lean</dt><dd class="declaration-name"><code>'
            + name + '</code></dd><dt>Import</dt><dd class="declaration-import">'
            + render_import(declaration) + "</dd></dl>"
        )

    def render_declaration_links(declaration, root):
        name = declaration["name"]
        module = declaration["module"]
        url = declaration["source_url"]
        if span := declaration.get("source_range"):
            first, _, last, end_column = span
            last_line = last if end_column else last - 1
            url += f"#L{first}" + (f"-L{last_line}" if last_line > first else "")
        return (
            '<p class="source-links">'
            + anchor("Module page", root + "modules/" + module + "/#" + name)
            + " · " + anchor("GitHub source ↗", url)
            + "</p>"
        )

    def render_declaration(declaration, root, *, show_header=True):
        name = declaration["name"]
        module = declaration["module"]
        source = ""
        if span := declaration.get("source_range"):
            path = module.replace(".", "/") + ".lean"
            if path not in library["source_hashes"]:
                raise ValueError(f"Unverified source for {name}")
            if path not in source_lines:
                source_lines[path] = (catalog.ROOT / path).read_text().split("\n")
            lines = source_lines[path]
            first, column, last, end_column = span
            if not (1 <= first <= last <= len(lines)
                    and 0 <= column <= len(lines[first - 1])
                    and 0 <= end_column <= len(lines[last - 1])
                    and (first, column) < (last, end_column)):
                raise ValueError(f"Invalid source range for {name}")
            snippet = lines[first - 1:last]
            snippet[-1] = snippet[-1][:end_column]
            snippet[0] = snippet[0][column:]
            source = "\n".join(snippet)
        signature = (
            '<pre class="lean-code" tabindex="0" aria-label="Compiled Lean type"><code>'
            + lean_code.highlight(declaration["type"]) + "</code></pre>"
        )
        body = signature
        if source:
            body = (
                '<details class="source-code"><summary>Lean source</summary>'
                '<pre class="lean-code" tabindex="0"><code>'
                + lean_code.highlight(source) + "</code></pre></details>"
                '<details class="compiled-type"><summary>Compiled type</summary>'
                + signature + "</details>"
            )
        if show_header:
            return (
                '<div class="declaration">'
                + render_declaration_identity(declaration)
                + render_declaration_links(declaration, root)
                + body + "</div>"
            )
        return body

    reading_order = [
        identifier
        for chapter in chapters
        for section_id in chapter["sections"]
        for identifier in sections[section_id]["entries"]
    ]
    positions = {identifier: index for index, identifier in enumerate(reading_order)}
    chapter_lookup = {chapter["id"]: chapter for chapter in chapters}
    numbers, section_numbers = {}, {}
    module_items, source_items, citations_by_module = {}, {}, {}
    declarations_by_module, citations_by_declaration = {}, {}
    for declaration in library["declarations"].values():
        declarations_by_module.setdefault(declaration["module"], []).append(declaration)
    for chapter_index, chapter in enumerate(chapters, 1):
        for section_index, section_id in enumerate(chapter["sections"], 1):
            section_number = f"{chapter_index}.{section_index}"
            section_numbers[section_id] = section_number
            for item_index, identifier in enumerate(sections[section_id]["entries"], 1):
                numbers[identifier] = f"{section_number}.{item_index}"
    for identifier, entry in entries.items():
        for name in entry["declarations"]:
            module = library["declarations"][name]["module"]
            module_items.setdefault(module, set()).add(identifier)
        for citation in entry["references"]:
            source_items.setdefault(citation["source"], set()).add(identifier)
    for citation in library.get("citations", []):
        module = library["declarations"][citation["name"]]["module"]
        citations_by_module.setdefault(module, []).append(citation)
        citations_by_declaration.setdefault(citation["name"], []).append(citation)

    def render_page(path, title, content, active_section="", breadcrumbs=(), overview=False):
        depth = len(Path(path).parts) - 1
        root = "../" * depth if depth else "./"
        active_chapter = chapter_lookup[sections[active_section]["chapter"]] if active_section else None
        focused = active_chapter is not None
        nav_label = "Chapter contents" if focused else "Library contents"
        navigation = ['<ul class="chapter-nav">']
        for chapter in [active_chapter] if focused else chapters:
            chapter_path = f'chapters/{chapter["id"]}/'
            current = ' aria-current="page"' if path == chapter_path + "index.html" else ""
            navigation.append(
                '<li class="nav-chapter">'
                f'<a class="nav-chapter-link" href="{root}{chapter_path}"{current}>'
                f'{prose(chapter["title"], root, links=False)}</a><ul class="section-nav">'
            )
            for section_id in chapter["sections"]:
                section = sections[section_id]
                section_path = f"sections/{section_id}/"
                current = (
                    ' aria-current="page"' if path == section_path + "index.html"
                    else ' aria-current="location"' if section_id == active_section
                    else ""
                )
                navigation.append(
                    f'<li><a class="nav-section link-row" href="{root}{section_path}"{current}>'
                    f'<span class="nav-section-title">{prose(section["title"], root, links=False)}</span> '
                    f'<span class="count">{section_numbers[section_id] if focused else len(section["entries"])}</span></a>'
                )
                if focused and section_id == active_section and section.get("topics"):
                    navigation.append(
                        '<ul class="topic-nav">'
                        + "".join(
                            "<li>" + prose_link(topic["title"],
                                root + section_path + "#" + topic["id"], root) + "</li>"
                            for topic in section["topics"]
                        )
                        + "</ul>"
                    )
                navigation.append("</li>")
            navigation.append("</ul></li>")
        navigation.append("</ul>")
        trail = [anchor("Library", root)]
        trail.extend(prose_link(label, root + href, root) for label, href in breadcrumbs)
        values = {
            "title": escape(library_text.plain_text(title) + " — Colib Library"),
            "root": root,
            "home": "true" if path == "index.html" else "false",
            "overview": "true" if overview else "false",
            "navigation": "".join(navigation),
            "nav_label": nav_label,
            "content": content,
            "breadcrumbs": (
                '<nav class="breadcrumbs" aria-label="Breadcrumb"><ol>'
                + "".join(f"<li>{link}</li>" for link in trail)
                + "</ol></nav>"
                if path != "index.html" else ""
            ),
            "revision": library["revision"],
            "short_revision": library["revision"][:7],
        }
        text = re.sub(r"\{\{([a-z_]+)\}\}", lambda match: values[match[1]], template)
        target = output / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def item_link(identifier):
        entry = entries[identifier]
        return prose_link(
            identifier + " · " + entry["title"], "../../tag/" + identifier + "/", "../../"
        )

    def render_item(identifier, root, heading="h2"):
        entry = entries[identifier]
        number = numbers[identifier]
        title = prose(entry["title"], root, links=False)
        if heading != "h1":
            title = "(" + title + ")"
        pieces = [
            f'<article class="item" id="{identifier}">',
            '<div class="item-statement">',
            '<header class="item-heading"><' + heading + '><span class="item-kind">'
            + escape(entry["kind"].title() + " " + number)
            + "</span> " + title
            + "</" + heading + '><span class="item-permalink">'
            + anchor(identifier, root + "tag/" + identifier + "/")
            + "</span></header>",
            '<div class="statement">' + prose(entry["statement"], root, paragraphs=True) + "</div>",
            "</div>",
        ]
        if entry.get("proof"):
            proof = prose(entry["proof"], root, paragraphs=True)
            if entry.get("proof_kind") == "proof":
                pieces.append('<section class="proof"><h3>Proof</h3>' + proof + '</section>')
            else:
                pieces.append(
                    '<details class="proof"><summary>Proof outline</summary>' + proof + '</details>'
                )
        first, *others = entry["declarations"]
        declaration = library["declarations"][first]
        pieces.extend([
            '<div class="item-implementation detail-stack">',
            render_declaration_identity(declaration),
            render_declaration_links(declaration, root),
            '<details class="scope-details"><summary>Scope and conventions</summary>'
            '<div class="scope">' + prose(entry["scope"], root, paragraphs=True)
            + "</div></details>",
            '<details class="item-details"><summary>Lean details</summary>'
            '<div class="item-details-body detail-stack">',
            render_declaration(declaration, root, show_header=False),
        ])
        if others:
            pieces.append(
                f'<p class="item-detail-heading">More Lean declarations ({len(others)})</p>'
                '<ul class="related-declarations detail-stack">'
            )
            for name in others:
                declaration = library["declarations"][name]
                pieces.append(
                    '<li><details><summary class="declaration-name"><code>'
                    + escape(name).replace(".", ".<wbr>")
                    + '</code></summary><div class="related-declaration-body detail-stack">'
                    '<dl class="declaration-identity"><dt>Import</dt><dd class="declaration-import">'
                    + render_import(declaration) + "</dd></dl>"
                    + render_declaration_links(declaration, root)
                    + render_declaration(declaration, root, show_header=False)
                    + "</div></details></li>"
                )
            pieces.append("</ul>")
        for field, label in (
            ("used_by", "Referenced by"),
            ("formal_dependencies", "Direct Lean references"),
        ):
            if ids := entry.get(field):
                pieces.append(
                    f'<details class="relations"><summary>{label}</summary><p>'
                    + " · ".join(anchor(value, root + "tag/" + value + "/") for value in ids)
                    + "</p></details>"
                )
        pieces.extend([
            "</div></details>",
            '<footer class="item-references"><details><summary>References</summary>',
            render_references(entry["references"], root),
        ])
        if heading == "h1":
            review = entry["review"].replace("_", "-")
            if checked := entry.get("source_checked_on"):
                review += " · " + checked
            pieces.append('<p class="review">Source correspondence · ' + escape(review) + "</p>")
        pieces.append("</details></footer></div></article>")
        return "".join(pieces)

    def render_section_item(section, identifier, heading="h2"):
        root = "../../"
        text = section.get("transitions", {}).get(identifier)
        transition = (
            '<div class="section-transition">' + prose(text, root, paragraphs=True) + "</div>"
            if text else ""
        )
        return transition + render_item(identifier, root, heading)

    home = [
        "<h1>Colib Library</h1>",
        '<p class="lede">The mathematical organization of Colib, from definitions and prerequisites '
        "to theorems, comparisons and their precise literature references.</p>",
        f'<p class="edition">{len(chapters)} chapters · {len(sections)} sections · {len(entries)} permanent items</p>',
        "<h2>Contents</h2>",
    ]
    for index, chapter in enumerate(chapters, 1):
        home.append(
            '<section class="chapter-overview"><h3>'
            + prose_link(f'{index}. {chapter["title"]}', "chapters/" + chapter["id"] + "/", "./")
            + "</h3><p>"
            + prose(chapter["introduction"], "./")
            + "</p><ol>"
        )
        for section_id in chapter["sections"]:
            section = sections[section_id]
            count = len(section["entries"])
            home.append(
                '<li><div class="link-row">'
                + prose_link(section["title"], "sections/" + section_id + "/", "./")
                + f'<span class="count">{count} {"item" if count == 1 else "items"}</span></div></li>'
            )
        home.append("</ol></section>")
    home.append(
        '<p class="contribute">Contribute through the '
        + anchor(
            "Library organization and contribution guide",
            "https://github.com/kangxyz/colib/blob/main/CONTRIBUTING.md",
        )
        + ".</p>"
    )
    render_page("index.html", "Contents", "".join(home))
    for chapter_index, chapter in enumerate(chapters, 1):
        body = (
            f'<p class="eyebrow">Chapter {chapter_index}</p><h1>'
            + prose(chapter["title"], "../../", links=False)
            + '</h1><p class="lede">'
            + prose(chapter["introduction"], "../../")
            + "</p>"
        )
        rows = []
        for section_id in chapter["sections"]:
            section = sections[section_id]
            number = section_numbers[section_id]
            path = "../../sections/" + section_id + "/"
            rows.append(
                '<li><span class="section-number">' + number + '</span><div>'
                + '<h3>' + prose_link(section["title"], path, "../../") + '</h3>'
                + prose(section["introduction"], "../../", paragraphs=True)
                + '</div></li>'
            )
        body += (
            '<nav class="chapter-contents" aria-labelledby="chapter-contents">'
            '<h2 id="chapter-contents">Contents</h2><ol>'
            + "".join(rows) + "</ol></nav>"
        )
        render_page("chapters/" + chapter["id"] + "/index.html", chapter["title"], body, overview=True)
    for section_id, section in sections.items():
        chapter = chapter_lookup[section["chapter"]]
        trail = [(chapter["title"], "chapters/" + chapter["id"] + "/")]
        body = (
            f'<header class="section-heading"><p class="eyebrow">Section {section_numbers[section_id]}</p><h1>'
            + prose(section["title"], "../../", links=False)
            + '</h1><div class="lede">'
            + prose(section["introduction"], "../../", paragraphs=True)
            + "</div></header>"
        )
        if topics := section.get("topics"):
            for topic in topics:
                body += (
                    f'<section class="topic" id="{topic["id"]}"><h2>'
                    + prose(topic["title"], "../../", links=False) + "</h2>"
                    + "".join(render_section_item(section, i, heading="h3") for i in topic["entries"])
                    + "</section>"
                )
        else:
            body += (
                '<ol class="section-contents">'
                + "".join(
                    "<li>"
                    + prose_link(
                        identifier + " · " + entries[identifier]["title"], "#" + identifier, "../../"
                    )
                    + "</li>"
                    for identifier in section["entries"]
                )
                + "</ol>"
                + "".join(render_section_item(section, i) for i in section["entries"])
            )
        render_page(
            "sections/" + section_id + "/index.html",
            section["title"],
            body,
            section_id,
            trail,
        )
        for identifier in section["entries"]:
            body = render_item(identifier, "../../", heading="h1")
            neighbors = []
            position = positions[identifier]
            if position:
                neighbors.append(
                    '<li><span>Previous</span>' + item_link(reading_order[position - 1]) + '</li>'
                )
            if position + 1 < len(reading_order):
                neighbors.append(
                    '<li><span>Next</span>' + item_link(reading_order[position + 1]) + '</li>'
                )
            body += (
                '<nav class="reading-nav" aria-label="Reading order"><ul>'
                + "".join(neighbors)
                + "</ul></nav>"
            )
            render_page(
                "tag/" + identifier + "/index.html",
                identifier + " · " + entries[identifier]["title"],
                body,
                section_id,
                [*trail, (section["title"], "sections/" + section_id + "/")],
            )
    for identifier, item in library.get("retired", {}).items():
        previous_url = ("https://github.com/kangxyz/colib/blob/"
                        + item["previous_revision"] + "/" + item["previous_path"])
        body = ("<h1>" + prose(identifier + " · " + item["title"], "../../", links=False)
                + '</h1><p class="lede">Retired Library item</p><p>'
                + prose(item["reason"], "../../") + "</p><p>"
                + anchor("Previous source record", previous_url) + "</p>")
        related = item.get("related_items", [])
        if related:
            body += "<p>Related maintained items: " + ", ".join(item_link(i) for i in related) + "</p>"
        render_page("tag/" + identifier + "/index.html", identifier + " · Retired", body)
    modules_index = [
        '<h1>Lean modules</h1><p class="lede">Browse Colib modules, their declarations and direct imports.</p>'
    ]
    for name, module in sorted(library["modules"].items()):
        matched = [
            entries[identifier]
            for identifier in sorted(module_items.get(name, set()), key=positions.get)
        ]
        body = (
            '<h1 class="module-title">'
            + escape(name)
            + "</h1><p>"
            + anchor("Lean source ↗", module["source_url"])
            + "</p>"
        )
        if matched:
            body += "<h2>Mathematical items</h2><ul>"
            body += (
                "".join("<li>" + item_link(entry["id"]) + "</li>" for entry in matched)
                + "</ul>"
            )
        owned = declarations_by_module.get(name, [])
        if owned:
            body += "<h2>Indexed declarations</h2>"
            for declaration in owned:
                body += (
                    '<details class="module-declaration" id="'
                    + escape(declaration["name"], quote=True)
                    + '"><summary>'
                    + escape(declaration["name"]) + "</summary>"
                    + render_declaration(declaration, "../../")
                    + "</details>"
                )
        module_citations = citations_by_module.get(name, [])
        if module_citations:
            body += "<h2>Literature references of declarations</h2>"
            by_declaration = {}
            for citation in module_citations:
                by_declaration.setdefault(citation["name"], []).append(citation)
            for declaration_name, citations in by_declaration.items():
                body += (
                    '<h3 class="reference-declaration">'
                    + anchor(declaration_name, "#" + declaration_name)
                    + "</h3>"
                    + render_references(citations, "../../")
                )
        body += "<h2>Direct imports</h2><ul>"
        for imported in module["imports"]:
            if imported in library["modules"]:
                body += "<li>" + anchor(imported, "../" + imported + "/") + "</li>"
            else:
                body += "<li><code>" + escape(imported) + "</code></li>"
        body += "</ul>"
        render_page(
            "modules/" + name + "/index.html",
            name,
            body,
            breadcrumbs=[("Lean modules", "modules/")],
        )
    module_tree = {}
    for name in sorted(library["modules"]):
        if name.partition(".")[0] != "Colib":
            continue
        branch = module_tree
        for part in name.split("."):
            branch = branch.setdefault(part, {})
        branch[""] = name

    def render_module_tree(branch):
        parts = ['<ul class="module-tree">']
        for label, child in branch.items():
            if not label:
                continue
            name = child.get("")
            title = anchor(label, name + "/") if name else escape(label)
            children = any(key for key in child)
            if children:
                parts.append(
                    "<li><details open><summary>"
                    + title
                    + "</summary>"
                    + render_module_tree(child)
                    + "</details></li>"
                )
            else:
                count = len(module_items.get(name, set()))
                parts.append(
                    '<li><div class="link-row">'
                    + title
                    + '<span class="count">'
                    + str(count)
                    + (" item" if count == 1 else " items")
                    + "</span></div></li>"
                )
        return "".join(parts) + "</ul>"

    modules_index.append(render_module_tree(module_tree))
    render_page("modules/index.html", "Lean modules", "".join(modules_index))

    def bibliography_line(source):
        parts = [", ".join(source["authors"])]
        for key, prefix in (("year", ""), ("journal", ""), ("volume", "vol. "), ("pages", "pp. ")):
            if value := source.get(key):
                parts.append(prefix + str(value))
        return escape(" · ".join(parts))

    sources_body = [
        '<h1>References</h1><p class="lede">Books, papers and reference works, with the inspected editions and exact item cross-references.</p>'
    ]
    source_order = {"reference_work": 1, "software": 2}
    ordered_sources = sorted(
        library["sources"].items(),
        key=lambda pair: (source_order.get(pair[1]["kind"], 0), pair[1]["title"]),
    )
    group = None
    for key, source in ordered_sources:
        source_group = source_order.get(source["kind"], 0)
        if source_group != group:
            group = source_group
            heading = {
                0: "Books and papers",
                1: "Reference works",
                2: "Implementation provenance",
            }[group]
            sources_body.append("<h2>" + heading + "</h2>")
        matched = [
            entries[identifier]
            for identifier in sorted(source_items.get(key, set()), key=positions.get)
        ]
        source_body = (
            "<h1>"
            + escape(source["title"])
            + "</h1><p>"
            + bibliography_line(source)
            + "</p><p>"
            + escape(source["version"])
            + "</p>"
        )
        source_body += "<p>" + anchor("Source record ↗", source["url"]) + "</p>"
        if source.get("doi"):
            source_body += "<p>DOI " + anchor(source["doi"], "https://doi.org/" + source["doi"]) + "</p>"
        for document in source.get("documents", []):
            source_body += (
                "<details><summary>"
                + escape(document["label"])
                + "</summary><p>"
                + anchor("Inspected document ↗", document["url"])
                + '</p><code class="digest">SHA-256 '
                + escape(document["sha256"])
                + "</code></details>"
            )
        if matched:
            source_body += "<h2>Library correspondence</h2><ul>"
            for entry in matched:
                source_body += "<li>" + item_link(entry["id"]) + "<ul>"
                locators = {
                    (ref["locator"], ref["url"]): ref
                    for ref in entry["references"]
                    if ref["source"] == key
                }
                source_body += (
                    "".join(
                        "<li>" + location_links(locators[locator], "../../") + "</li>"
                        for locator in sorted(locators)
                    )
                    + "</ul></li>"
                )
            source_body += "</ul>"
        else:
            source_body += "<p>Implementation provenance is recorded in the owning item and source documentation.</p>"
        render_page(
            "references/" + key + "/index.html",
            source["title"],
            source_body,
            breadcrumbs=[("References", "references/")],
        )
        label = source["title"] + " · " + source["kind"].replace("_", " ")
        sources_body.append(
            '<section class="source"><h2>'
            + anchor(label, key + "/")
            + "</h2><p>"
            + bibliography_line(source)
            + "</p><p>"
            + escape(source["version"])
            + "</p>"
            + f"<p>{len(matched)} indexed mathematical items</p></section>"
        )
    render_page("references/index.html", "References", "".join(sources_body))
    render_page(
        "search/index.html",
        "Search",
        '<h1>Search the Library</h1><p id="search-status" role="status">Search by item, statement, Lean declaration or source locator.</p><div id="search-results"></div>',
    )
    search = []
    for entry in entries.values():
        terms = [
            entry["id"],
            entry["title"],
            entry["statement"],
            *entry["declarations"],
        ]
        for reference in entry["references"]:
            source = library["sources"][reference["source"]]
            terms.extend(
                [
                    reference["source"],
                    reference["locator"],
                    source["title"],
                    *source["authors"],
                ]
            )
        search.append(
            {
                "id": entry["id"],
                "title": entry["title"],
                "kind": entry["kind"],
                "section": sections[entry["section"]]["title"],
                "path": "tag/" + entry["id"] + "/",
                "statement": entry["statement"],
                "terms": " ".join(terms).casefold(),
            }
        )
    for identifier, item in library.get("retired", {}).items():
        search.append({
            "id": identifier, "title": item["title"], "kind": "retired",
            "section": "Retired items", "statement": item["reason"],
            "terms": " ".join([identifier, item["title"], item["reason"]]).casefold(),
        })
    for record in search:
        record["path"] = "tag/" + record["id"] + "/"
        record["title_html"] = prose(record["title"], "../", links=False)
        record["statement_html"] = prose(record["statement"], "../")
        record["section"] = library_text.plain_text(record["section"])
        plain_terms = " ".join(
            library_text.plain_text(record[field]).casefold() for field in ("title", "statement")
        )
        record["terms"] += f' {plain_terms} {normalize("NFKC", plain_terms)}'
    for name, module in library["modules"].items():
        search.append(
            {
                "title": name,
                "kind": "module",
                "section": "Lean modules",
                "statement": "Defining module and its direct imports.",
                "terms": (" ".join([name, *module["imports"]])).casefold(),
                "path": "modules/" + name + "/",
            }
        )
    tagged_names = {
        name for entry in entries.values() for name in entry["declarations"]
    }
    for name, declaration in library["declarations"].items():
        if name in tagged_names:
            continue
        terms = [name, declaration["module"]]
        for citation in citations_by_declaration.get(name, []):
            source = library["sources"][citation["source"]]
            terms.extend(
                [
                    source["title"],
                    citation["source"],
                    citation["locator"],
                    *source["authors"],
                ]
            )
        search.append(
            {
                "title": name,
                "kind": "declaration",
                "section": declaration["module"],
                "statement": declaration["type"],
                "terms": " ".join(terms).casefold(),
                "path": "modules/" + declaration["module"] + "/#" + name,
            }
        )
    (output / "search.json").write_text(json.dumps(search, ensure_ascii=False) + "\n")
    for name in ("style.css", "site.js"):
        shutil.copyfile(catalog.ROOT / "docs/site" / name, output / name)
    (output / "library.json").write_text(
        json.dumps(library, ensure_ascii=False, indent=2) + "\n"
    )
    (output / "catalog.json").write_text(json.dumps(library, ensure_ascii=False) + "\n")
    (output / ".nojekyll").touch()
    print(
        f"Built the Library contents, {len(chapters)} chapters, {len(sections)} sections, "
        f'{len(entries)} item pages and {len(library["sources"])} reference pages'
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--library", type=Path, default=Path("build/library/library.json")
    )
    parser.add_argument("--output", type=Path, default=Path("build/site"))
    args = parser.parse_args()
    build(args.library, args.output)
