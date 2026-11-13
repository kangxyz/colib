/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarRefinementDifference
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.GeometricImage
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Basic

/-! # Original lifting and boundary image from actual extension corrections

Section-specific corrections are restricted along their actual evaluation
squares, compared with native scalar sections, and traced before quotienting.
This consumer does not construct the geometric refinements or the finite-field
presentation witnesses, and does not assert a covering or epimorphism family.
-/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FiniteSeparableDescent.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `dbb5ef2c83bc8d99c4e479d6a57da1ab3c9a9dc1`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.PresheafWithTransfers

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

/-- Actual sectionwise extension corrections give lifting on the original
presheaf; the quantified correction inputs remain explicit hypotheses. -/
theorem HasRestrictionDifferenceLifting.of_coprime_refinements
    {k E L : Type u} [Field k] [Field E] [Field L]
    [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E]
    [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]
    (P : PresheafWithTransfers.{u + 1} k)
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) [Flat β.left] (α : O ⟶ A) [Flat α.left] (φ : O ⟶ D)
    (hE : ∀ s, Nonempty (FiniteSeparableRefinementCorrection P E β α φ s))
    (hL : ∀ s, Nonempty (FiniteSeparableRefinementCorrection P L β α φ s))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    HasRestrictionDifferenceLifting P φ β α := by
  intro s
  obtain ⟨wE⟩ := hE s
  obtain ⟨wL⟩ := hL s
  exact exists_restriction_difference_of_coprime_refinements P β α φ s wE wL hdegree

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k)
variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]
variable {L : Type u} [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Two section-specific extension corrections give the original canonical image
witness. The flat correction legs follow from the actual open/etale square. -/
theorem imageSieve_of_coprime_finiteSeparable_refinements
    {W W' : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left}
    (V : EtaleSeparatedFiniteType X.left) (b : W' ⟶ (cylinderNeighborhood X).obj V)
    (z : V.left ⟶ W'.left)
    (hz : z ≫ b.left =
      (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left)
    (O : SmoothSite (Spec (.of k)))
    (α : O ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W')
    (β : O ⟶ SmoothSite.Contraction.torusCylinder.obj ((toSmoothSite X).obj V))
    (H : IsPullback β.left α.left
      (SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj V)).left b.left)
    (f : W' ⟶ W)
    (φ : O ⟶ (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
      ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W))
    (hφ₁ : φ.left ≫ pullback.fst W.hom
      (SmoothSite.Contraction.openInclusion.app X).left = α.left ≫ f.left)
    (hφ₂ : φ.left ≫ pullback.snd W.hom
      (SmoothSite.Contraction.openInclusion.app X).left = β.left ≫
        (SmoothSite.productMap (toBase X V)
          (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))).left)
    (s : sections P (Cor.mk ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
      ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W))))
    (wE : FiniteSeparableRefinementCorrection P E β α φ s)
    (wL : FiniteSeparableRefinementCorrection P L β α φ s)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    Presheaf.imageSieve (contractionToBoundary X P).hom
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
        (SmoothSite.Contraction.openInclusion.app X)
        (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)).app (op W) s)
      (geometricZeroLift X V b z hz ≫
        (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map f) := by
  have hb : Etale (b.left ≫ ((cylinderNeighborhood X).obj V).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  let : Etale b.left := Etale.of_comp b.left ((cylinderNeighborhood X).obj V).hom
  let : IsOpenImmersion α.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      H inferInstance
  let : Etale β.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) H.flip inferInstance
  obtain ⟨a, c, h⟩ := exists_restriction_difference_of_coprime_refinements
    P β α φ s wE wL hdegree
  exact imageSieve_of_geometric_difference X V b z hz P O α β H f φ hφ₁ hφ₂ s a c h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
