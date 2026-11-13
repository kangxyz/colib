/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.IsoAmbient
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.GeometricRefinement
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialOverlap
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialTorusLifting
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.SmoothNeighborhood

/-!
# The original boundary image from a marked polynomial lift

The marked lift supplies its actual étale chart and signed equation.
Transport the chart through the native cylinder and torus isomorphisms
to obtain the image witness on the original open arrow.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/PolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
  (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
  (R : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))}
  (p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)) [Etale p.left]
  (w : Spec (.of R))
  (s₀ : Spec (.of R) ⟶ Y.left)
  (v₀ : SmoothSite.affineSite k R ⟶
    (toSmoothSite X).obj ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).obj W))
  [IsOpenImmersion v₀.left]
  (e₀ : Y ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W)
  (hp : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.Contraction.affineLineCylinder.map
        (v₀ ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).obj W)) =
      e₀ ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W)
  (hmark : s₀ ≫ e₀.left = v₀.left ≫
    pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left)

include hp hmark in
/-- The original marked affine lift gives an image witness for each original section. -/
theorem exists_polynomial_boundary_image_neighborhood_of_lifting
    (hLift : HasAffinePolynomialTorusLifting R p w P s₀)
    (d : ((PresheafWithTransfers.toPresheaf k).obj P).obj (op
      ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
        ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W)))) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (v : V ⟶ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W),
      IsOpenImmersion v.left ∧ v₀.left w ∈ Set.range v.left ∧
      Presheaf.imageSieve (contractionToBoundary X P).hom
        ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
          (SmoothSite.Contraction.openInclusion.app X)
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)).app (op W) d) v := by
  obtain ⟨B, v, _hB, hv, hw, E, η, q, ζ, _hE, _hη, hq, hbase, hζq, hζη,
    O, α, β, φ, H, hφ, hL⟩ := hLift
  let : IsOpenImmersion v.left := hv
  let : Etale q.left := hq
  let W₀ := (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W
  let fB := (v ≫ v₀) ≫ toBase X W₀
  let : Etale fB.left := by
    change Etale ((v.left ≫ v₀.left) ≫ W₀.hom)
    infer_instance
  let V := ofSmoothMap X B fB
  let eB := ofSmoothMapIso X B fB
  let eL := cylinderIso eB
  let eT := (SmoothSite.Contraction.parameterProduct
    (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).mapIso eB
  let v' : V ⟶ W₀ := MorphismProperty.Over.homMk (v.left ≫ v₀.left) rfl
  let q' := q ≫ eL.hom
  let η' := η ≫ e₀
  let : IsIso eL.hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eL).hom)
  let : Etale q'.left := by
    change Etale (q.left ≫ eL.hom.left)
    infer_instance
  have hqbase : η' ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W =
      q' ≫ SmoothSite.Contraction.affineLineCylinder.map (toBase X V) := by
    calc
      _ = η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
          SmoothSite.Contraction.affineLineCylinder.map (v₀ ≫ toBase X W₀) := by
        simpa only [η', Category.assoc] using congrArg (fun h => η ≫ h) hp.symm
      _ = q ≫ SmoothSite.Contraction.affineLineCylinder.map v ≫
          SmoothSite.Contraction.affineLineCylinder.map (v₀ ≫ toBase X W₀) := by
        simpa only [Category.assoc] using congrArg
          (fun h => h ≫ SmoothSite.Contraction.affineLineCylinder.map (v₀ ≫ toBase X W₀)) hbase
      _ = q ≫ SmoothSite.Contraction.affineLineCylinder.map fB := by
        rw [← SmoothSite.Contraction.affineLineCylinder.map_comp]
        simp only [fB, Category.assoc]
      _ = q' ≫ SmoothSite.Contraction.affineLineCylinder.map (toBase X V) := by
        change _ = (q ≫ SmoothSite.Contraction.affineLineCylinder.map eB.hom) ≫
          SmoothSite.Contraction.affineLineCylinder.map (toBase X V)
        rw [Category.assoc, ← SmoothSite.Contraction.affineLineCylinder.map_comp,
          ofSmoothMapIso_toBase]
  have he : η'.left ≫ W.hom = q'.left ≫ ((cylinderNeighborhood X).obj V).hom :=
    congrArg (fun f => f.left) hqbase
  let W' := geometricRefinementNeighborhood X V E q'
  let eE := geometricRefinementIso X V E q'
  let f := geometricRefinementToOriginal X V E q' η' he
  let b := geometricRefinementToCylinder X V E q'
  let α' := α ≫ eE.hom
  let β' := β ≫ eT.hom
  let τ := polynomialOverlapToPunctured X (v₀ ≫ toBase X W₀) W p e₀ hp
  let φ' := φ ≫ τ
  have hz : ζ ≫ b.left =
      (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left := by
    change ζ ≫ (q.left ≫ eL.hom.left) = _
    rw [← Category.assoc, hζq]
    have h := congrArg (fun f => f.left)
      (SmoothSite.Contraction.nativeAffineSection_naturality (.of k) eB.hom 0)
    change (SmoothSite.Contraction.nativeAffineSection (.of k) B 0).left ≫ eL.hom.left =
      𝟙 B.left ≫ (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V)
        0).left at h
    exact h.trans (Category.id_comp _)
  have hzη : ζ ≫ η'.left = v'.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left := by
    change ζ ≫ (η.left ≫ e₀.left) = (v.left ≫ v₀.left) ≫ _
    rw [← Category.assoc, hζη, Category.assoc, hmark, ← Category.assoc]
  have H' : IsPullback β'.left α'.left
      (SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj V)).left b.left := by
    apply H.of_iso (Iso.refl O.left)
      ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eT)
      ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eE)
      ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eL)
    · change β.left ≫ eT.hom.left = 𝟙 O.left ≫ (β.left ≫ eT.hom.left)
      rw [Category.id_comp]
    · change α.left ≫ eE.hom.left = 𝟙 O.left ≫ (α.left ≫ eE.hom.left)
      rw [Category.id_comp]
    · exact congrArg (fun f => f.left)
        (SmoothSite.Contraction.openInclusion.naturality eB.hom).symm
    · change q.left ≫ eL.hom.left = 𝟙 E.left ≫ (q.left ≫ eL.hom.left)
      rw [Category.id_comp]
  have hφ₁ : φ'.left ≫ pullback.fst W.hom
      (SmoothSite.Contraction.openInclusion.app X).left = α'.left ≫ f.left := by
    have hφleft : φ.left ≫ (SmoothSite.etalePullbackFst p
        (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R))
        ).left = α.left ≫ η.left :=
      congrArg (fun f => f.left) hφ
    change (φ.left ≫ τ.left) ≫ pullback.fst W.hom
      (SmoothSite.Contraction.openInclusion.app X).left = (α.left ≫ 𝟙 E.left) ≫ η'.left
    rw [Category.comp_id, Category.assoc, polynomialOverlapToPunctured_fst,
      ← Category.assoc, hφleft]
    change (α.left ≫ η.left) ≫ e₀.left = α.left ≫ (η.left ≫ e₀.left)
    exact Category.assoc _ _ _
  have hφ₂ : φ'.left ≫ pullback.snd W.hom
      (SmoothSite.Contraction.openInclusion.app X).left = β'.left ≫
        (SmoothSite.productMap (toBase X V)
          (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))).left := by
    apply (cancel_mono (SmoothSite.Contraction.openInclusion.app X).left).mp
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hφ₁]
    have hf : f.left ≫ W.hom = b.left ≫ ((cylinderNeighborhood X).obj V).hom := he
    rw [Category.assoc, hf, ← Category.assoc, ← H'.w, Category.assoc]
    simpa only [Category.assoc] using
      congrArg (fun h => β'.left ≫ h) (contractionOpen_base_isPullback X V).w
  have hL' := PresheafWithTransfers.HasRestrictionDifferenceLifting.restrict P hL τ
  have hL'' := PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_right P hL' eT
  have hL''' := PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_ambient P hL'' eE
  obtain ⟨a, c, hac⟩ := hL''' d
  have hi := imageSieve_of_geometric_difference X V b ζ hz P O α' β' H' f φ'
    hφ₁ hφ₂ d a c hac
  have hzv := geometricRefinement_zero_arrow X V E q' η' he ζ hz v' hzη
  rw [hzv] at hi
  refine ⟨V, v', ?_, ?_, hi⟩
  · change IsOpenImmersion (v.left ≫ v₀.left)
    infer_instance
  · obtain ⟨y, hy⟩ := hw
    refine ⟨y, ?_⟩
    change v₀.left (v.left y) = v₀.left w
    rw [hy]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
