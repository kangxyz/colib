/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenStructure
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionWaldhausen
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionReindex
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Original coefficient reindexing for relative-open sections

The genuine geometric pullback along an arbitrary commuting open-pair square is exact.
The actual original evaluation-transition isomorphism transports that exactness to arrow
evaluation. Literal coefficient reindexing therefore preserves the original coarse weak class,
as well as the unchanged fine cofibrations, zero and pushouts. No cartesian or flatness premise
is needed, and geometric evaluation remains naturally isomorphic rather than strictly natural.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt

include l h in
/-- The original coefficient-arrow evaluation is exact for the actual relative-open structures. -/
theorem boundedAboveFlatAffineEvaluationAt_open_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSectionOpenWaldhausen j).cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      (boundedAboveFlatPerfectOpenWaldhausen j').cof (boundedAboveFlatPerfectOpenWaldhausen j').weq
      (boundedAboveFlatAffineEvaluationAt R (Under.mk f)) :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatAffineSectionOpenWaldhausen j) (boundedAboveFlatPerfectOpenWaldhausen j')
    ((boundedAboveFlatAffineSectionOpenEvaluation_coarse_exact j).comp
      (boundedAboveFlatPerfectOpenPullback_isExact
        (boundedAboveFlatAffineSupportedPairSquare j j' f l h)))
    (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f))

include l h in
/-- The unchanged coefficient functor is exact for every specified original open-pair square. -/
theorem boundedAboveFlatAffineSectionsMap_open_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSectionOpenWaldhausen j).cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      (boundedAboveFlatAffineSectionOpenWaldhausen j').cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j').weq
      (boundedAboveFlatAffineSectionsMap f) where
  zero := (boundedAboveFlatAffineSectionsMap_exact f).zero
  cofibration := (boundedAboveFlatAffineSectionsMap_exact f).cofibration
  pushout := (boundedAboveFlatAffineSectionsMap_exact f).pushout
  weak a ha := by
    change (boundedAboveFlatPerfectOpenWaldhausen j').weq
      ((boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S).map a)
    rw [boundedAboveFlatAffineSectionsMap_comp_evaluation]
    exact (boundedAboveFlatAffineEvaluationAt_open_exact j j' f l h).weak a ha

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenReindexExact.lean:36-61"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineEvaluationAt_open_exact
  boundedAboveFlatAffineSectionsMap_open_exact

end AlgebraicGeometry.Scheme.Modules
