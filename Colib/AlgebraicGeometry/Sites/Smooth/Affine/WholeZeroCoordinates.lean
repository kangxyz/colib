/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineZeroCoordinates

/-! # Full zero fibers in canonical affine coordinates

The actual native additive cylinder is unchanged. Its canonical comparison to
polynomial coordinates transports the whole Cartesian zero scheme, not a
reduced support. This supplies the arbitrary-affine adapter used by both the
infinite and finite original-boundary constructions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

/-- Canonical affine coordinates identify literal evaluation with native zero. -/
@[reassoc] theorem affineLineIso_zero
    (B : SmoothSite (Spec (.of k))) [IsAffine B.left] :
    lineZero (k := k) (R := Γ(B.left, ⊤)) ≫ (affineLineIso B).hom =
      (affineIso B).hom ≫ nativeAffineSection (.of k) B 0 := by
  change lineZero ≫ (lineCylinderIso.hom ≫
    affineLineCylinder.map (affineIso B).hom) = _
  rw [← Category.assoc, lineZero_cylinder, nativeAffineSection_naturality]

/-- The unchanged entire zero fiber is Cartesian in the literal polynomial chart. -/
theorem affineLineIso_wholeZero_isPullback
    (B : SmoothSite (Spec (.of k))) [IsAffine B.left]
    {E : Scheme.{u}} (q : E ⟶ (affineLineCylinder.obj B).left)
    (a : B.left ⟶ E)
    (H : IsPullback a (𝟙 B.left) q (nativeAffineSection (.of k) B 0).left) :
    IsPullback ((affineIso B).hom.left ≫ a) (𝟙 _)
      (q ≫ (affineLineIso B).inv.left)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(B.left, ⊤))))) := by
  apply H.of_iso'
    ((forgetScheme (Spec (.of k))).mapIso (affineIso B)) (Iso.refl E)
    ((forgetScheme (Spec (.of k))).mapIso (affineIso B))
    ((forgetScheme (Spec (.of k))).mapIso (affineLineIso B))
  · exact (Category.comp_id ((affineIso B).hom.left ≫ a)).symm
  · exact (Category.comp_id (affineIso B).hom.left).trans
      (Category.id_comp (affineIso B).hom.left).symm
  · change 𝟙 E ≫ q = (q ≫ (affineLineIso B).inv.left) ≫ (affineLineIso B).hom.left
    rw [Category.id_comp, Category.assoc]
    rw [show (affineLineIso B).inv.left ≫ (affineLineIso B).hom.left = 𝟙 _ from
      congrArg (fun f => f.left) (affineLineIso B).inv_hom_id, Category.comp_id]
  · exact (congrArg (fun f => f.left) (affineLineIso_zero B)).symm

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
