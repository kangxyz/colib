# Native exterior composition milestone: 209 source contribution snapshot

Snapshot time: 2026-11-10T09:17:05.783133+00:00. Baseline: `184ad8bc877d722314a5464fa53fbff82b4428c8` (tree `4a25e8e1d9e64f289666ecab1c70529d80fd6a14`).

The actual signed exterior composition theorem is now fully checked: smooth X, Y and Z over a field and geometrically integral parameter T; the existing nativeExterior commutes with the existing incidenceTorPairing on all signed native finite correspondences. Every generic label keeps its own dimension and finite residue degree. The proof adds no perfection, separability, reduced-incidence, support-flatness, coefficient-regularity or global-equidimensionality assumption.

This increment publishes the actual stalk/Koszul/Tor comparison, length and Euler-coefficient comparison, geometric pullback identification, finite cycle push-pull and final composition. The final lane contains 24 fully checked sources (13 production, 11 actual consumers; 320 native declarations). The current core export contains 50 fully checked sources (30 production, 20 actual consumers; 1258 native owner declarations). These lane counts overlap previously published sources and are not additional-to-209 counts. Against the 174-source checkpoint, there are 35 new sources and one already-published PushPull consumer strengthened with two directly applied theorem examples. All 22 new production imports are added to the root.

The snapshot contains 209 Lean module files only, with 118 production files and 91 actual consumers. It is a source overlay, not a standalone project. Its ZIP contains no reports, manifests, root import hubs, scripts, compiled artifacts or dependencies. The separate source manifest records every source hash.

Validation reuses the exact existing native receipts: actual included producers and consumers compiled, all 15 native declaration linters, ordinary-axiom closure and exact textstyle passed. Source hashes and publication dependencies were checked; no new test was run for this backup. No new aggregate root build or kernel replay was run. This checkpoint intentionally skips CI. The successful CI of historical main 581293ea does not certify later main heads.

One independent test file is deliberately excluded: ColibTest/NativeExteriorIncidenceStalkBaseChange.lean. Its four explicit geometric quotient specializations still hit an elaboration heartbeat limit, despite all supporting production owners being checked. Its failed candidate is not included or counted as accepted, and is not needed by the published production dependency closure. The complete 51-source core test packet is therefore not claimed complete.

Pins remain Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 and Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7. Native validation used the preserved provider e7697ab8164435c7093665d02ac34f021eefb75e plus exact source overlays. Existing dependencies match the frozen baseline, with no additional unpublished Colib dependency.

Transfer singular/sheaf-complex assembly, canonical motivic-complex endpoints, genuine weight-one quasi-isomorphism and strict A1 invariance remain unfinished. This is the completed exterior-composition milestone, not a whole-motivic completion claim. The branch does not replace or overwrite live main or the other contributor's intervening work.
