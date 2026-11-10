# Integral torus identity axis: 276-source checkpoint

Snapshot: 2026-11-10T13:05:26.910868+00:00. Live-main baseline: `76a00f7f5cfec1ab3fc25ff28f8db0493f508b4a`. Previous contribution checkpoint: `14854f4360f21d1d776939e6fb42f3a6bcf724d5`.

This branch-only increment adds three accepted Lean sources: two production modules and one actual consumer with four examples. They establish integral-source correspondence base change and the actual integral torus identity-axis comparison using native scheme and presheaf-with-transfers objects. General hypotheses, integral-source requirements and the actual geometric maps are retained. This stage does not claim the full weight-one theorem, strict A1 invariance, or completion of the motivic migration.

The exact three sources passed compilation, all fifteen native declaration linters, ordinary-axiom closure for 42 declarations, and exact selected-source textstyle. Publication selects the accepted v19 source snapshot, reusing the byte-identical v16 IntegralSource and v18 TorusIdentityAxisIntegral products. Acceptance, source, artifact and static actual-closure checks are reused without a new Lean frontend. External dependency seals are reused rather than rehashing entire packages. Native validation, source correspondence and independent mathematical review remain distinct.

All prior 273 contribution source bytes are unchanged. The separate ZIP contains exactly 276 Lean modules, 167 production and 109 actual consumers, excluding the root hub, documentation, reports, manifests, dependencies and build outputs. ZIP SHA-256: `75b633411c7749622cee98c8187c58c3e4ff7a71d0001047d2108ea5a44b972e`.

Actual source-import closure reaches 17248 modules, with 210 lower Colib sources byte-identical to live main and 1 historical metadata-only remaps preserved. No unpublished mathematical dependency is introduced. Two sorted production imports are added to the canonical root. Existing Library chapters, item IDs, citations, workflows, tools and other source remain unchanged. No permanent Library tags are added.

Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and Stacks `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` remain pinned. This checkpoint uses [skip ci] and does not update main or trigger another CI run. Main remains on the separately published 273-source milestone; later main integration will batch this accepted stage with further completed cycle or rational-function work. No local Lean, Lake, tests, cache/bootstrap or kernel replay is invoked.
