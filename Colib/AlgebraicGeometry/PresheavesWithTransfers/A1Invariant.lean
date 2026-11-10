/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-!
# Coefficient homotopy invariance on the actual affine projection

The active model uses the native additive parameter. Its predicate is proved
equivalent to the original polynomial-spectrum projection predicate, using
the actual cylinder comparison and not an unspecified isomorphism of values.
No ordinary singular-chain homotopy theorem is substituted for coefficient HI.
Adapted from `Motivic/Cohomology/A1/Basic.lean:33-144`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u v w

namespace AlgebraicGeometry.A1
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable (R : CommRingCat.{u}) {A : Type w} [Category.{v} A]

/-- Restriction along the actual native affine-cylinder projection. -/
def projectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (X : SmoothSite (Spec R)) :
    P.obj (op X) ⟶ P.obj (op (affineLineCylinder.obj X)) :=
  P.map ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).op

/-- Restriction along literal polynomial evaluation, expressed in native coordinates. -/
def sectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (X : SmoothSite (Spec R)) (a : R) :
    P.obj (op (affineLineCylinder.obj X)) ⟶ P.obj (op X) :=
  P.map (nativeAffineSection R X a).op

@[reassoc (attr := simp)]
theorem projectionPullback_sectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (X : SmoothSite (Spec R)) (a : R) :
    projectionPullback R P X ≫ sectionPullback R P X a = 𝟙 _ := by
  simp only [projectionPullback, sectionPullback, ← P.map_comp, ← op_comp,
    nativeAffineSection_projection, op_id, P.map_id]

/-- HI concerns the actual projection map, not the existence of some value isomorphism. -/
def IsInvariant (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) : Prop :=
  ∀ X : SmoothSite (Spec R), IsIso (projectionPullback R P X)

/-- The actual original polynomial projection followed by comparison is the native projection. -/
@[reassoc]
theorem polynomialProjectionPullback_comparison
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) (X : SmoothSite (Spec R)) :
    P.map (SmoothSite.productFst X (polynomialAffineLine R)).op ≫
      (P.mapIso (affineCylinderPolynomialIso R X).op).hom =
        projectionPullback R P X := by
  change P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp, Iso.op_hom, ← op_comp, affineCylinderPolynomialIso_hom_projection]

/-- The native coefficient predicate is exactly the original polynomial-spectrum one. -/
theorem isInvariant_iff_polynomial_projection
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) :
    IsInvariant R P ↔ ∀ X : SmoothSite (Spec R),
      IsIso (P.map (SmoothSite.productFst X (polynomialAffineLine R)).op) := by
  constructor
  · intro h X
    let := h X
    have : IsIso (P.map (SmoothSite.productFst X (polynomialAffineLine R)).op ≫
        (P.mapIso (affineCylinderPolynomialIso R X).op).hom) := by
      rw [polynomialProjectionPullback_comparison]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (P.mapIso (affineCylinderPolynomialIso R X).op).hom
  · intro h X
    let := h X
    rw [← polynomialProjectionPullback_comparison]
    infer_instance

/-- The section comparison retains the original evaluation map after pullback. -/
@[reassoc]
theorem polynomialSectionPullback_comparison
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) (X : SmoothSite (Spec R)) (a : R) :
    (P.mapIso (affineCylinderPolynomialIso R X).op).hom ≫ sectionPullback R P X a =
      P.map (polynomialAffineSection R X a).op := by
  change P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp, Iso.op_hom, ← op_comp, nativeAffineSection_polynomialIso]

/-- Every coefficient section is the inverse when the projection is invertible. -/
theorem sectionPullback_projectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) (a : R) :
    sectionPullback R P X a ≫ projectionPullback R P X = 𝟙 _ := by
  let := hP X
  apply (cancel_epi (projectionPullback R P X)).mp
  simp [← Category.assoc]

end AlgebraicGeometry.A1

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Coefficient HI on the actual graph-restricted presheaf. -/
def IsA1Invariant (P : PresheafWithTransfers.{v} k) : Prop :=
  A1.IsInvariant (.of k) ((toPresheaf k).obj P)

/-- The predicate isequivalent to the original coefficient projection, with actual graphs. -/
theorem isA1Invariant_iff_polynomial_projection (P : PresheafWithTransfers.{v} k) :
    IsA1Invariant P ↔ ∀ X : SmoothSite (Spec (.of k)),
      IsIso (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productFst X (SmoothSite.Contraction.polynomialAffineLine (.of k))))) :=
  A1.isInvariant_iff_polynomial_projection (.of k) ((toPresheaf k).obj P)

@[simp]
theorem a1ProjectionPullback_eq_transfer (P : PresheafWithTransfers.{v} k)
    (X : SmoothSite (Spec (.of k))) :
    A1.projectionPullback (.of k) ((toPresheaf k).obj P) X =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productFst X (SmoothSite.additiveGroupObject (Spec (.of k))))) := rfl

end AlgebraicGeometry.PresheafWithTransfers
