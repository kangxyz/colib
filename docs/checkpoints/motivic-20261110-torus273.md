# Native torus geometry: 273-source checkpoint

Snapshot: 2026-11-10T12:46:30.298492+00:00. Live-main baseline: `22adfaf92dc0bb17ddb9a3b00fe759d92ff04286`. Previous contribution checkpoint: `4aa464abcb406264b60438a5a6ac7497b3bc7990`.

This increment adds six accepted Lean sources: five production modules and one actual consumer with 14 examples. They construct native torus unit points, finite-flat polynomial spans and linear graphs, quotient stalk multiplicities, and actual determinant-norm comparisons. General commutative-ring hypotheses and explicit unit conditions are retained. This is a concrete affine geometric stage, not the whole weight-one theorem, strict A1 invariance, or completion of the motivic migration. The separate identity-axis packet is not part of this checkpoint.

The exact six sources passed compilation, all fifteen native declaration linters, ordinary-axiom closure for 93 declarations, and exact selected-source textstyle. Publication uses the accepted v14 sources, with the byte-identical v2 quotient-stalk product reused. It verifies acceptance, source and artifact hashes and invokes no new Lean frontend. External dependency seals are reused rather than rehashing entire packages. Author source correspondence, native validation and independent mathematical review remain distinct.

The prior 267 contribution sources remain byte-identical. The separate pure source ZIP has exactly 273 Lean modules, 165 production and 108 actual consumers, excluding the root hub, documentation, reports, manifests, dependencies and build outputs. ZIP SHA-256: `ca59fde856129b7d7bdd4b1a8986debae6b6125495d7488bbd575396f30748e7`.

Actual source-import closure reaches 9041 modules, with 15 lower Colib sources byte-identical to live main and 0 preserved historical tag-only remaps. No unpublished mathematical dependency is introduced. Five sorted production imports are added to the canonical root. Library chapters, item IDs, citations, workflow/tooling files, all other source and concurrent main work remain unchanged. These supporting modules add no permanent Library tags.

Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and Stacks `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` remain pinned. The checkpoint uses [skip ci]. Authorized normal main integration preserves ordered parents and triggers one natural CI run, with exact-head status recorded separately and no dispatch or rerun. No local Lean, Lake, tests, cache/bootstrap or kernel replay is invoked.
