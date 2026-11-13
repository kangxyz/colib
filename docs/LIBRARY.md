# Colib Library

The [Library](https://kangxyz.github.io/colib/) is Colib's mathematical organization centre.
It owns the chapter and section sequence, permanent mathematical items, chosen-model
explanations, stated scope and literature crosswalk. Lean files own the checked definitions and proofs.
The chapter structure and source dependency graph express their respective mathematical roles.

## Maintained owners

| Information | Owner |
| --- | --- |
| Chapters, sections, topics and reading transitions | docs/library/chapters/*.toml |
| Mathematical statements, kinds, conditions and correspondence review state | docs/library/entries/<chapter>/<ID>.toml |
| Retired permanent IDs and their previous source records | docs/library/retired/<ID>.toml |
| Declaration membership in a mathematical item | The compiled `@[colib_tag "COL-0004"]` attribute |
| Stacks correspondence | Mathlib's existing `@[stacks TAG "scope"]` attribute |
| Book and paper correspondence | `@[colib_ref "key" "locator" "relation" "scope"]` |
| Bibliographic identity, edition, document and version | docs/references.toml |
| Declaration types, defining modules, source ranges and implementation references | Native Lean export |
| Reading pages, reverse references, search and links | Generated Library website |

One item can have several implementing declarations and several literature references.
An implementation can serve several explicitly registered items. When a Library item uses
an upstream declaration directly, attach its attributes in the Colib module that develops
the corresponding mathematics. The declaration keeps its original defining module.

## Structure and permanent links

Chapters contain sections. Each section has an introduction and an ordered sequence of typed
items such as definitions, lemmas, theorems and comparisons. The homepage presents the table of
contents. A chapter page lists its sections with a short description of the mathematical
work in each. The section page presents the results in reading order, with a local
chapter and topic navigation. The Modules tree lists Colib modules. Declaration and
import links can open indexed upstream modules. Each item has its own page at
`tag/COL-0004/`, with exact citations, Lean declarations and automatically exported code
references. Existing
`#COL-0004` bookmarks redirect to the permanent item page.

For a longer section, use `[[sections.topics]]` in its chapter file. Give each topic an
`id`, `title` and `start` item from that section. The first topic starts at the first item,
and later topics begin in the section's reading order. The chapter page gives the section
contents, and section pages group the results under those topics.

Use `[sections.transitions]` for passages that connect results in a section. Key each
passage by the permanent ID of the item it precedes. It appears before that item in the
section reading page and the Markdown catalog. At a change of topic, explain how the
next construction enters the argument. Between related items, name the map,
calculation or hypothesis from the preceding result that the reader should carry
forward. For example, the passage before COL-0033 identifies the kernel of the row
\([-f,p]\) as the way to transport a pullback by preserving conflations. Keep these
passages short enough to read alongside the statements. Write them as mathematical
prose. Introduce the notation needed for the calculation, state the hypotheses at
the point they are used, and justify an intermediate step by the calculation itself
or a reference to the exact result that supplies it.

Keep the section introduction focused on the objects and question of the section.
Use topics to group parts of the argument and use transitions where the reader
needs to carry data from one part to another. When moving an item, check the topic
boundary and any section transition keyed by its ID.

When moving an item between sections, keep its permanent ID and record it in
`legacy_items = ["COL-0004"]` on the previous section. Keep the previous section
slug and URL. The generated page retains a visible fallback link at the old
fragment; the site also redirects old item fragments to the permanent `tag/`
page. An item cannot be both current and legacy in the same section. Moving a
whole section between chapters preserves its `sections/<slug>/` URL.

IDs start with COL- and at least four decimal digits. They are independent of chapter numbers,
Lean names and file paths. Moving an item preserves its ID. Released IDs are never reused.
A substantive replacement records the relation to the earlier item explicitly. Reading positions
can change without changing permanent links.

Removing a maintained item moves its identifier to `docs/library/retired/<ID>.toml`.
The `[retired]` record contains its `id`, `title`, `reason`, exact `previous_revision`,
`previous_path` and optional `related_items`. Retired IDs cannot be reused, have no active
Lean binding, and keep a searchable permanent page linking to the previous source record.
Related items are reading suggestions, not assertions that the retired theorem is equivalent
to a replacement. `catalog.py show` also resolves retired IDs.

Only occupied mathematical chapters and source families are created. The migration programme
in docs/MIGRATION.md identifies upcoming cohomological and homotopical work. A new chapter is
introduced with its first concrete mathematical contribution and source owner.

## References in Lean

Use existing Stacks syntax for a Stacks statement and Colib's general reference attribute for
a book or paper. Each bibliographic key resolves through docs/references.toml.

```lean
@[colib_tag "COL-0004", stacks 00JE "finite-module dimension equivalence",
  colib_ref "WeibelKBook" "II, section 2, field computation" "adaptation"
    "The categorical Grothendieck group of finite modules over a field"]
def fgModuleRankEquiv ... := ...
```

A citation records the particular clause, hypothesis range and mathematical construction being
used. A definition, an input theorem, its proof and a later comparison have their actual reference
roles and scope. Several references can be attached to the same declaration. The exporter reads
these compiled attributes and checks all keys and locators against the maintained bibliography.

Retain native EGA and SGA attributes when an applicable upstream declaration already has them.
The supported website export currently indexes Stacks and the general Colib bibliography
attribute. Extend the exporter with an actual indexed consumer when adding another database.

Code provenance identifies an earlier implementation independently of the cited mathematics.
A result proved in Colib can state its original contribution and cite background accurately.
An unchecked attribution is marked `citation needed` in its mathematical draft. An unresolved
mathematical premise is stated as an obligation in the owning source family.

## Math and citations in Library prose

Use English title case for chapter names. In titles, introductions, statements, scopes and
proof outlines, use the same formatting for each kind of content.

State the ambient objects, hypotheses, maps and conclusion in the statement. Introduce
notation where it first enters the argument and use the same symbols for the same maps
throughout the section. For a comparison, give its action on the generators or other
data that determine it, with the direction, coefficient map and sign where relevant.
Use `scope` for the chosen model, additional conditions and implementation conventions.
When shortening a statement, carry its precise hypotheses, maps and normalizations
into the statement, scope or proof as appropriate.

Separate paragraphs with blank lines. A `proof` can be a proof outline or a complete
argument. Set `proof_kind = "proof"` for a complete argument displayed with the statement.
Keep the proof or proof outline before the Lean information. Place the Lean declaration
name and import together, followed by links to the defining module and source.
The site reads the declaration data from the native export. For a Colib
declaration with a Lean source range it also shows the corresponding text from the checked
source and links to that line range. Upstream bindings show their compiled types and link
to the defining modules at the pinned revisions. A result with several bindings can
select its primary declaration with `primary`, which must name one of its compiled bindings.
Place **Scope and conventions** after the source links, directly above **Lean details**.
Both start closed. Open **Lean details** for the implementation and related declarations.
The additional declarations appear by name and open individually. **Lean source**,
**Compiled type**, **Referenced by** and **Direct Lean references** start closed where
the corresponding data exists. **References** is a single disclosure that starts closed.
It contains the works, precise locators and correspondence scopes. Locators for the same
work with the same scope and relation share one entry.
Use `source_checked_on` for a previously recorded author source-check date in YYYY-MM-DD
format. The page displays the date with the correspondence status.

- Write inline mathematics as `\(...\)` or `$...$` and display mathematics as
  `\[...\]` or `$$...$$`. For example, use `\(K_0\)` and `\((-1)^{pq}\)`.
  Use KaTeX-supported commands and enclose an entire expression in one pair of delimiters.
- Enclose literal Lean identifiers and expressions in backticks. Use a TOML literal
  string for prose with TeX backslashes, or escape each backslash in a basic string.
  In Lean reference scopes, a dollar-delimited formula can use the usual Lean string syntax.
- Write an existing permanent ID such as `COL-0004` to link to its item page. Write
  `[@WeibelKBook]` for the bibliography record or `[@WeibelKBook, II, Definition 6.1.1]`
  for a specific locator. Use `[@stacks, Tag 02MU]` for a Stacks Project tag and
  `[@stacks, Tag 02MX(1)]` when referring to a numbered clause.

```toml
statement = 'Dimension identifies \(K_0(k)\) with \(\mathbb{Z}\).'
scope = 'The presentation is [@stacks, Tag 02MU], applied to `FGModuleCat k`.'
```

Prose citations are reading links. Compiled `@[stacks]` and `@[colib_ref]` attributes own
declaration attribution and its precise scope. Use the existing bibliographic key for the
inspected edition, and give the exact theorem, clause, page or code location. Use
`short_title` for a concise inline label and `title` for the full bibliography heading.

For software, use a repository-relative Lean file, with the exact line or inclusive range
where available, such as `Aglib/RingTheory/MvPolynomial/RegularSequence.lean:36-71`.
Separate disjoint line spans with commas. Check each path and line against the commit in
the bibliography. The recorded `locator_roots` normalize existing paths relative to a
source library. For books and papers, keep the printed locator and use the inspected
document selected by that source record.

Run `python3 scripts/catalog.py check` after editing prose. It checks delimiter pairing,
bibliography keys, permanent IDs and source URL syntax. The native export also checks
compiled citation scopes and resolves source locators. Preview a page with each new
formula or citation pattern to check its KaTeX rendering and link destination.

## Dependencies and status

Lean's module system owns code organization and imports. The native exporter reads defining
modules and their direct imports, and records constants used in registered declaration types
and bodies. Item pages link the registered results occurring among those direct references.
The section sequence provides the reading order.

`@[colib_tag]` has the single purpose of attaching a permanent webpage identifier to a public
mathematical item. Helpers use ordinary Lean names. An agent adds a tag when a result needs a
stable, independently citable Library page. The tag preserves its link through a declaration
rename or source move. An ordinary supporting declaration can carry a literature citation
without a permanent tag; its references appear on its module page. Books and papers use `@[colib_ref]`, and Stacks uses its native tag.

The native exporter determines which registered declarations exist in the built environment.
A successful production build and axiom audit retain their checked source and scope.
`author_checked` records the author's literature correspondence check. Independent mathematical
review has its own evidence and checked span. CI validates metadata integrity and native
compilation; maintainers assess mathematical correspondence and source applicability.

## Contribution transaction

A mathematical contribution updates its Lean source, item and chapter ownership, references and
applicable tests together. The Library is the first route for finding an existing result and the
place where its new public mathematical surface is registered. Internal supporting lemmas belong
to that same owner. CONTRIBUTING.md defines assignments, style and incremental validation.

## Item schema and agent lookup

Each file contains one `[entry]` table. A contribution uses an allocated identifier and an
existing section owner, as in docs/library/entries/k-theory-rings/COL-0004.toml.

```toml
[entry]
id = "COL-0004"
title = "K₀ of finite-dimensional vector spaces"
kind = "theorem"
section = "grothendieck-groups"
order = 40
statement = "Dimension identifies the Grothendieck group with the integers."
scope = "Finite-dimensional vector spaces over a field, with the specified object classes."
review = "author_checked"
```

Use `python3 scripts/catalog.py show COL-0004` to locate the item and chapter. A compatible
native export also supplies its actual Lean declarations and defining modules. Use
`rg 'colib_tag "COL-0004"' Colib` to find its compiled bindings. The website's reference
index finds all items attached to a book, paper or Stacks locator.

Place a new mathematical file under its native Mathlib-style subject. New chapters and sections
need an introduction and an actual first item. Code ownership and imports are read from Lean.
Native tag bindings must resolve to maintained item IDs. Every published item has a
compiled precise reference, and every citation key has one bibliographic record.

The first literature records include Weibel's online chapters II and III of *The K-book* and
Milnor's 1970 paper *Algebraic K-theory and quadratic forms*. The inspected documents and hashes
are recorded beside their bibliographic identity. Reference annotations retain exact clauses
and the scope of any adaptation or comparison.

Bibliographic keys use letters, digits, underscores and hyphens, beginning with a letter.
Chapter, section and item orders are nonnegative integers.
