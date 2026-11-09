/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionZero
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionMorphismClasses
public import Colib.CategoryTheory.Waldhausen.EquivalenceStructure

/-!
# The actual pointwise Waldhausen structure and exact coefficient restriction

Adapted from the corresponding bounded-flat section constructions in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native geometric objects and structures.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open CategoryTheory.GrothendieckZeroSections
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Genuine section Waldhausen structure, retaining the original pointwise chosen zero. -/
@[colib_tag "COL-0355"]
def boundedAboveFlatAffineSectionWaldhausen (R : CommRingCat.{u}) :
    Waldhausen.Structure (BoundedAboveFlatAffineSections R) :=
  (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).ofEquivalence
    (boundedAboveFlatAffineSectionEquivalence R) (boundedAboveFlatAffineSectionZero R) (by
      change IsZero ((boundedAboveFlatAffineOriginalEvaluation R).obj
        (boundedAboveFlatAffineSectionZero R))
      rw [boundedAboveFlatAffineOriginalEvaluation_sectionZero]
      exact (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero)

/-- The actual cofibrations are exactly the original pointwise cofibrations. -/
theorem boundedAboveFlatAffineSectionWaldhausen_cof_iff (R : CommRingCat.{u})
    {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) :
    (boundedAboveFlatAffineSectionWaldhausen R).cof a ↔ boundedAboveFlatAffineSectionCof R a :=
  (boundedAboveFlatAffineSectionCof_iff R a).symm

/-- The actual weak equivalences are exactly the original pointwise weak equivalences. -/
theorem boundedAboveFlatAffineSectionWaldhausen_weq_iff (R : CommRingCat.{u})
    {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) :
    (boundedAboveFlatAffineSectionWaldhausen R).weq a ↔ boundedAboveFlatAffineSectionWeq R a :=
  (boundedAboveFlatAffineSectionWeq_iff R a).symm

/-- The original identity evaluation is genuinely Waldhausen-exact. -/
theorem boundedAboveFlatAffineOriginalEvaluation_exact (R : CommRingCat.{u}) :
    Waldhausen.IsExact (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).weq
      (boundedAboveFlatAffineOriginalEvaluation R) :=
  Waldhausen.Structure.ofEquivalence_exact _ _ _ _

/-- Every actual coefficient-arrow evaluation is exact, by original geometric pullback. -/
theorem boundedAboveFlatAffineEvaluationAt_exact (R : CommRingCat.{u}) (j : Under R) :
    Waldhausen.IsExact (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq
      (boundedAboveFlatAffineEvaluationAt R j) where
  zero h := ((boundedAboveFlatPerfectPullback_isExact (Spec.map j.hom)).zero
    ((boundedAboveFlatAffineOriginalEvaluation_exact R).zero h)).of_iso
      ((boundedAboveFlatAffineEvaluationPullbackIso R j).app _).symm
  cofibration a h := ((boundedAboveFlatAffineSectionWaldhausen_cof_iff R a).mp h) j
  weak a h := ((boundedAboveFlatAffineSectionWaldhausen_weq_iff R a).mp h) j
  pushout hi h := by
    have hp := (boundedAboveFlatPerfectPullback_isExact (Spec.map j.hom)).pushout
      ((boundedAboveFlatAffineOriginalEvaluation_exact R).cofibration _ hi)
      ((boundedAboveFlatAffineOriginalEvaluation_exact R).pushout hi h)
    let e := boundedAboveFlatAffineEvaluationPullbackIso R j
    exact hp.of_iso (e.app _) (e.app _) (e.app _) (e.app _)
      (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

/-- The chosen Waldhausen zero is the source-independent pointwise zero section. -/
theorem boundedAboveFlatAffineSectionWaldhausen_zero (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineSectionWaldhausen R).zero = boundedAboveFlatAffineSectionZero R := rfl

/-- The actual inverse of the proved evaluation equivalence is also Waldhausen-exact. -/
theorem boundedAboveFlatAffineSectionEquivalence_inverse_exact (R : CommRingCat.{u}) :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).weq
      (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatAffineSectionEquivalence R).inverse :=
  Waldhausen.Structure.ofEquivalence_inverse_exact _ _ _ _

/-- Every actual coefficient restriction is exact for the genuine pointwise Waldhausen structures.
-/
@[colib_tag "COL-0355",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionReindexExact.lean:25-54"
    "adaptation" "Exact coefficient restriction for every ring map, using cofibration pushouts"]
theorem boundedAboveFlatAffineSectionsMap_exact {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Waldhausen.IsExact (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatAffineSectionWaldhausen S).cof
      (boundedAboveFlatAffineSectionWaldhausen S).weq
      (boundedAboveFlatAffineSectionsMap φ) where
  zero h := by
    have hz : IsZero ((boundedAboveFlatAffineSectionsMap φ).obj
        (boundedAboveFlatAffineSectionZero R)) := by
      rw [boundedAboveFlatAffineSectionsMap_sectionZero]
      exact isZero_boundedAboveFlatAffineSectionZero S
    exact hz.of_iso ((boundedAboveFlatAffineSectionsMap φ).mapIso
      (h.iso (isZero_boundedAboveFlatAffineSectionZero R)))
  cofibration a ha := by
    change (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).cof
      ((boundedAboveFlatAffineSectionsMap φ ⋙ boundedAboveFlatAffineOriginalEvaluation S).map a)
    rw [boundedAboveFlatAffineSectionsMap_comp_evaluation]
    exact (boundedAboveFlatAffineEvaluationAt_exact R (Under.mk φ)).cofibration a ha
  weak a ha := by
    change (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).weq
      ((boundedAboveFlatAffineSectionsMap φ ⋙ boundedAboveFlatAffineOriginalEvaluation S).map a)
    rw [boundedAboveFlatAffineSectionsMap_comp_evaluation]
    exact (boundedAboveFlatAffineEvaluationAt_exact R (Under.mk φ)).weak a ha
  pushout {A B D P} {i f g j} hi h := by
    apply IsPushout.of_map_of_faithful (boundedAboveFlatAffineOriginalEvaluation S)
    change IsPushout
      ((boundedAboveFlatAffineSectionsMap φ ⋙ boundedAboveFlatAffineOriginalEvaluation S).map i)
      ((boundedAboveFlatAffineSectionsMap φ ⋙ boundedAboveFlatAffineOriginalEvaluation S).map f)
      ((boundedAboveFlatAffineSectionsMap φ ⋙ boundedAboveFlatAffineOriginalEvaluation S).map g)
      ((boundedAboveFlatAffineSectionsMap φ ⋙ boundedAboveFlatAffineOriginalEvaluation S).map j)
    rw [boundedAboveFlatAffineSectionsMap_comp_evaluation]
    exact (boundedAboveFlatAffineEvaluationAt_exact R (Under.mk φ)).pushout hi h

end AlgebraicGeometry.Scheme.Modules
