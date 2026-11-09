# Actual affine-section Bass telescope correspondence

Original Quillen revision: c561118b7795eb9780be9ed391c3251d6a4d0afd.
Native baseline: current mathematical main plus frozen COL-0359, COL-0360 and COL-0361.

## Exact owners and clauses

- `Quillen/Topology/Prespectrum/TelescopeDiagram.lean:25-74`: native generic
  `Topology.LoopPrespectrum.Telescope.diagramFunctor`, its cylinder action, natural stage
  inclusions and literal inclusion homotopy. Same-time naturality is the cylinder formula.
- `Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassDiagram.lean:25-38` and
  `SectionBassTransition.lean:24-49`: native concrete Tower owner, actual frozen affine seed
  and endofunctor. The successor convention is Bass followed by the previous iterate, exactly
  as in the original. No new seed is chosen and all coefficient maps are retained.
- `SectionBassTelescope.lean:26-85`: native concrete Telescope owner. Its levels are the
  existing reduced quotient telescope, not another colimit-space model. Its cylinder time
  remains independent of the prespectrum structure-loop time.
- `SectionBassTopology.lean:27-29,40-43,55-58`: only T1 clauses. Original Waldhausen values
  give initial T1, finite strict Bass separation gives every iterate, and native telescope
  separation gives the actual quotient. The unrelated point-HEP clauses are not migrated.
- `SectionBassStableColimit.lean:29-112`: actual finite-stage stable diagram, coefficient
  functor and colimit functor, canonical iso, all stage-leg equations, full naturality, and
  whole NatIso. Its forward map remains native `colimit.desc` of the actual inclusions.

## Exact boundary

Every signed integer degree is included. Concrete public declarations assume no supplied
seed, diagram, all-level separation profile, point HEP, closed embedding, cofibration or
geometric evaluation comparison. No COL-0358 dependency is used. Arbitrary coefficient maps
include the nonflat and noninjective integers-to-ZMod-2 map.

This is the ambient section construction. It does not identify its groups with classical Bass
negative groups or another telescope model, nor assert supported localization, evaluation
stable equivalence, telescope cone excision or Thomason--Trobaugh 7.4. In particular the original
`SectionBassTelescopeNaturality` owner is later cone-excision work and is not used here.

Frozen seed consumers already verify the two Laurent charts, original forward unit action,
right-associated reverse-null/unit/null word and its degree-zero coordinates. New consumers
only test the tower/telescope/stable-colimit endpoint and do not replace those prerequisites.

Source correspondence and compilation are separate evidence. This record describes the source
comparison; build receipts and the final freeze record establish the compiled source revision.
