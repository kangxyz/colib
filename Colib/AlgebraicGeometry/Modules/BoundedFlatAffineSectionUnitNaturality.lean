/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionUnit

/-!
# Pointwise unit action and strict coefficient naturality

Evaluation at every original coefficient arrow carries the section automorphism to multiplication
by the pulled-back original global unit. The actual evaluation transition proves this formula.
It implies strict naturality under literal coefficient reindexing, without a replacement action.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt
  boundedAboveFlatPerfectGlobalUnitIso

/-- Every original arrow evaluation sees the original pulled-back global-unit scalar. -/
@[colib_tag "COL-0359",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      SectionUnitNaturality.lean:31-46"
    "adaptation" "All-coefficient scalar formula via the actual evaluation transition"]
theorem boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSections R) (j : Under R) :
    (boundedAboveFlatAffineEvaluationAt R j).map
        ((boundedAboveFlatAffineSectionUnitIso R r).hom.app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec j.right)
        (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).hom.app
          ((boundedAboveFlatAffineEvaluationAt R j).obj s) := by
  have h₁ := boundedAboveFlatAffineEvaluationPullbackIso_naturality R
    ((boundedAboveFlatAffineSectionUnitIso R r).hom.app s) j
  rw [boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_hom,
    boundedAboveFlatPerfectPullback_map_globalUnit] at h₁
  have h₂ := (boundedAboveFlatPerfectGlobalUnitIso (Spec j.right)
    (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).hom.naturality
      ((boundedAboveFlatAffineEvaluationPullbackIso R j).hom.app s)
  simp only [Functor.id_map] at h₂
  exact (cancel_epi ((boundedAboveFlatAffineEvaluationPullbackIso R j).hom.app s)).mp
    (h₁.symm.trans h₂.symm)

/-- The entire evaluated automorphism is the original geometric pulled-back unit automorphism. -/
theorem boundedAboveFlatAffineEvaluationAt_mapIso_sectionUnitIso (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSections R) (j : Under R) :
    (boundedAboveFlatAffineEvaluationAt R j).mapIso
        ((boundedAboveFlatAffineSectionUnitIso R r).app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec j.right)
        (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).app
          ((boundedAboveFlatAffineEvaluationAt R j).obj s) := by
  exact Functor.IdentityAutomorphism.mapIso_app_eq
    (boundedAboveFlatAffineEvaluationAt R j) (boundedAboveFlatAffineSectionUnitIso R r)
    (boundedAboveFlatPerfectGlobalUnitIso (Spec j.right)
      (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)) s
    (boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom R r s j)

/-- The inverse section action retains the inverse original scalar at every coefficient arrow. -/
theorem boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_inv (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSections R) (j : Under R) :
    (boundedAboveFlatAffineEvaluationAt R j).map
        ((boundedAboveFlatAffineSectionUnitIso R r).inv.app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec j.right)
        (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).inv.app
          ((boundedAboveFlatAffineEvaluationAt R j).obj s) := by
  exact Functor.IdentityAutomorphism.map_inv_app_eq
    (boundedAboveFlatAffineEvaluationAt R j) (boundedAboveFlatAffineSectionUnitIso R r)
    (boundedAboveFlatPerfectGlobalUnitIso (Spec j.right)
      (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)) s
    (boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom R r s j)

/-- The actual section automorphism commutes with every original transition of its section. -/
theorem boundedAboveFlatAffineSectionUnitIso_section_naturality (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSections R) {i j : Under R} (a : i ⟶ j) :
    let φ : s ⟶ s := (boundedAboveFlatAffineSectionUnitIso R r).hom.app s
    s.obj.val.map a ≫ φ.hom.val.app j = φ.hom.val.app i ≫ s.obj.val.map a := by
  exact (fun φ : s ⟶ s ↦ φ.hom.val.naturality a)
    ((boundedAboveFlatAffineSectionUnitIso R r).hom.app s)

/-- Original units commute strictly with literal coefficient restriction of sections. -/
@[colib_tag "COL-0359",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      SectionUnitNaturality.lean:83-99"
    "adaptation" "Strict arbitrary coefficient naturality of the actual section unit"]
theorem boundedAboveFlatAffineSectionUnitIso_coefficient_hom {R S : CommRingCat.{u}}
    (f : R ⟶ S) (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionUnitIso R r).hom
        (boundedAboveFlatAffineSectionsMap f) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineSectionUnitIso S
          (Units.map (Spec.map f).appTop.hom.toMonoidHom r)).hom := by
  exact Functor.IdentityAutomorphism.whisker_hom_eq_of_evaluation
    (boundedAboveFlatAffineSectionsMap f) (boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatAffineEvaluationAt R (Under.mk f))
    (boundedAboveFlatAffineSectionsMap_comp_evaluation f)
    (boundedAboveFlatAffineSectionUnitIso R r)
    (boundedAboveFlatAffineSectionUnitIso S (Units.map (Spec.map f).appTop.hom.toMonoidHom r))
    (boundedAboveFlatPerfectGlobalUnitIso (Spec S)
      (Units.map (Spec.map f).appTop.hom.toMonoidHom r))
    (fun s ↦ boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom R r s (Under.mk f))
    (boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_hom S
      (Units.map (Spec.map f).appTop.hom.toMonoidHom r))

/-- The entire unit isomorphism commutes strictly with arbitrary coefficient reindexing. -/
theorem boundedAboveFlatAffineSectionUnitIso_coefficient {R S : CommRingCat.{u}}
    (f : R ⟶ S) (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.isoWhiskerRight (boundedAboveFlatAffineSectionUnitIso R r)
        (boundedAboveFlatAffineSectionsMap f) =
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineSectionUnitIso S
          (Units.map (Spec.map f).appTop.hom.toMonoidHom r)) := by
  apply Iso.ext
  exact boundedAboveFlatAffineSectionUnitIso_coefficient_hom f r

/-- The inverse unit action also commutes strictly with arbitrary coefficient reindexing. -/
theorem boundedAboveFlatAffineSectionUnitIso_coefficient_inv {R S : CommRingCat.{u}}
    (f : R ⟶ S) (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionUnitIso R r).inv
        (boundedAboveFlatAffineSectionsMap f) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineSectionUnitIso S
          (Units.map (Spec.map f).appTop.hom.toMonoidHom r)).inv :=
  congrArg Iso.inv (boundedAboveFlatAffineSectionUnitIso_coefficient f r)

end AlgebraicGeometry.Scheme.Modules
