/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback

/-!
# Pointwise affine section cofibrations and weak equivalences

Adapted from the corresponding bounded-flat section constructions in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native geometric objects and structures.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Cofibrations at every actual coefficient arrow. -/
def boundedAboveFlatAffineSectionCof (R : CommRingCat.{u}) :
    MorphismProperty (BoundedAboveFlatAffineSections R) := fun _ _ a =>
  ∀ j : Under R, (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof
    ((boundedAboveFlatAffineEvaluationAt R j).map a)

/-- Original weak equivalences at every actual coefficient arrow. -/
def boundedAboveFlatAffineSectionWeq (R : CommRingCat.{u}) :
    MorphismProperty (BoundedAboveFlatAffineSections R) := fun _ _ a =>
  ∀ j : Under R, (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq
    ((boundedAboveFlatAffineEvaluationAt R j).map a)

/-- Actual identity evaluation detects and preserves every pointwise cofibration. -/
theorem boundedAboveFlatAffineSectionCof_iff (R : CommRingCat.{u})
    {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) :
    boundedAboveFlatAffineSectionCof R a ↔
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).cof
        ((boundedAboveFlatAffineOriginalEvaluation R).map a) := by
  constructor
  · intro h
    have hh := h (Under.mk (𝟙 R))
    rw [boundedAboveFlatAffineEvaluationAt_id] at hh
    exact hh
  · intro h j
    let e := boundedAboveFlatAffineEvaluationPullbackIso R j
    have hm : (boundedAboveFlatAffineEvaluationAt R j).map a =
        e.inv.app s ≫ (boundedAboveFlatPerfectPullback (Spec.map j.hom)).map
          ((boundedAboveFlatAffineOriginalEvaluation R).map a) ≫ e.hom.app t := by
      change (boundedAboveFlatAffineEvaluationAt R j).map a = e.inv.app s ≫
        ((boundedAboveFlatAffineOriginalEvaluation R ⋙
          boundedAboveFlatPerfectPullback (Spec.map j.hom)).map a ≫ e.hom.app t)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof.comp_mem _ _
      ((boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof_iso _ inferInstance)
      ((boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof.comp_mem _ _
        ((boundedAboveFlatPerfectPullback_isExact (Spec.map j.hom)).cofibration _ h)
        ((boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof_iso _ inferInstance))

/-- Actual identity evaluation detects and preserves every pointwise weak equivalence. -/
theorem boundedAboveFlatAffineSectionWeq_iff (R : CommRingCat.{u})
    {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) :
    boundedAboveFlatAffineSectionWeq R a ↔
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).weq
        ((boundedAboveFlatAffineOriginalEvaluation R).map a) := by
  constructor
  · intro h
    have hh := h (Under.mk (𝟙 R))
    rw [boundedAboveFlatAffineEvaluationAt_id] at hh
    exact hh
  · intro h j
    let e := boundedAboveFlatAffineEvaluationPullbackIso R j
    have hm : (boundedAboveFlatAffineEvaluationAt R j).map a =
        e.inv.app s ≫ (boundedAboveFlatPerfectPullback (Spec.map j.hom)).map
          ((boundedAboveFlatAffineOriginalEvaluation R).map a) ≫ e.hom.app t := by
      change (boundedAboveFlatAffineEvaluationAt R j).map a = e.inv.app s ≫
        ((boundedAboveFlatAffineOriginalEvaluation R ⋙
          boundedAboveFlatPerfectPullback (Spec.map j.hom)).map a ≫ e.hom.app t)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq.comp_mem _ _
      ((boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq_iso _ inferInstance)
      ((boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq.comp_mem _ _
        ((boundedAboveFlatPerfectPullback_isExact (Spec.map j.hom)).weak _ h)
        ((boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq_iso _ inferInstance))

end AlgebraicGeometry.Scheme.Modules
