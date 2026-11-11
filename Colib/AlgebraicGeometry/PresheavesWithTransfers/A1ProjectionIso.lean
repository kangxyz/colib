/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant

/-!
# Projection isomorphisms for homotopy-invariant coefficients

The actual native projection and constant sections are those of the existing
coefficient predicate. Adapted from `Motivic/Cohomology/A1/Basic.lean:71-112`
at motivic@a6805c4a87cdfd7717dd7a94039246a167f15380.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u v w

namespace AlgebraicGeometry.A1
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable (R : CommRingCat.{u}) {A : Type w} [Category.{v} A]

/-- The actual projection is the forward map of the HI isomorphism. -/
def projectionIso (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) (hP : IsInvariant R P)
    (X : SmoothSite (Spec R)) :
    P.obj (op X) ≅ P.obj (op (affineLineCylinder.obj X)) := by
  letI := hP X
  exact asIso (projectionPullback R P X)

@[simp]
theorem projectionIso_hom (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) :
    (projectionIso R P hP X).hom = projectionPullback R P X := rfl

/-- Every actual constant section gives the inverse. -/
theorem projectionIso_inv (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) (a : R) :
    (projectionIso R P hP X).inv = sectionPullback R P X a := by
  apply (cancel_epi (projectionIso R P hP X).hom).mp
  exact (projectionIso R P hP X).hom_inv_id.trans
    (projectionPullback_sectionPullback R P X a).symm

/-- Projection pullback is natural in the actual smooth-site map. -/
@[reassoc]
theorem projectionPullback_naturality (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    P.map f.op ≫ projectionPullback R P X =
      projectionPullback R P Y ≫ P.map (affineLineCylinder.map f).op := by
  simp only [projectionPullback, ← P.map_comp, ← op_comp]
  exact congrArg (fun g ↦ P.map g.op)
    ((projection (SmoothSite.additiveGroupObject (Spec R))).naturality f).symm

/-- Inverse projection isomorphisms are natural in smooth-site maps. -/
@[reassoc]
theorem projectionIso_inv_naturality (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    P.map (affineLineCylinder.map f).op ≫ (projectionIso R P hP X).inv =
      (projectionIso R P hP Y).inv ≫ P.map f.op := by
  apply (cancel_epi (projectionIso R P hP Y).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [show (projectionIso R P hP Y).hom ≫ P.map (affineLineCylinder.map f).op =
    P.map f.op ≫ (projectionIso R P hP X).hom from
      (projectionPullback_naturality R P f).symm]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.A1

