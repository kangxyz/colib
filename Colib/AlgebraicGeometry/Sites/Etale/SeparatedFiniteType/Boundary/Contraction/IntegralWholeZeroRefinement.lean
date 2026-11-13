/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.WholeZeroRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso

/-! # Integral affine bases for the original whole-zero neighborhood refinements

The integral base is an actual componentwise affine open containing the chosen
point of the original zero fiber. A second whole-closed-fiber refinement retains
the ambient map and the entire new zero fiber; no integrality of the original
smooth object or rationality of its points is assumed.
-/

/-! Adapted from `Motivic/Cohomology/A1/Contraction/IntegralWholeZeroRefinement.lean`,
blob `2ca5810deb506441596186edf730b018a2f4d577` at motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- Whole-zero refinements may have an actual integral affine base neighborhood,
while preserving the original ambient, cylinder and closed-fiber maps. -/
theorem exists_integral_whole_zero_neighborhood_refinement
    (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
    (w : ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W).left) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (v : V ⟶ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W),
      IsAffine V.left ∧ IsIntegral V.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
        (e : E ⟶ W) (q : E ⟶ (cylinderNeighborhood X).obj V)
        (a : V.left ⟶ E.left)
        (zV : V ⟶ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj E),
        IsAffine E.left ∧ Etale q.left ∧ QuasiCompact q.left ∧ IsSeparated q.left ∧
        IsPullback a (𝟙 V.left) q.left
          (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left ∧
        zV.left ≫ pullback.fst E.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left
= a ∧
        zV ≫ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map q =
          zeroNeighborhoodLift X V ∧
        zV ≫ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map e = v
:= by
  obtain ⟨V, v, hV, hv, hw, E, e, q, a, zV, hE, hq, _hqc, hqs, H, haz, _hzq, hze⟩ :=
    exists_whole_zero_neighborhood_refinement X W w
  let : IsAffine V.left := hV
  let : IsAffine E.left := hE
  let : Etale q.left := hq
  let : IsSeparated q.left := hqs
  let : IsOpenImmersion v.left := hv
  obtain ⟨v₀, hv₀⟩ := hw
  let C := SmoothSite.integralAffineCover k ((toSmoothSite X).obj V)
  let i := Scheme.Cover.idx C v₀
  obtain ⟨t, ht⟩ := Scheme.Cover.covers C v₀
  let U : EtaleSeparatedFiniteType X.left := MorphismProperty.Over.mk ⊤ (C.f i ≫ V.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let b : U ⟶ V := MorphismProperty.Over.homMk (C.f i) rfl
  have : IsAffine U.left := inferInstanceAs (IsAffine (C.X i))
  have : IsIntegral U.left := inferInstanceAs (IsIntegral (C.X i))
  have : IsOpenImmersion b.left := inferInstanceAs (IsOpenImmersion (C.f i))
  let v' := b ≫ v
  have hv' : IsOpenImmersion v'.left := inferInstanceAs (IsOpenImmersion (C.f i ≫ v.left))
  have hw' : w ∈ Set.range v'.left := by
    refine ⟨t, ?_⟩
    change v.left (C.f i t) = w
    rw [ht, hv₀]
  let L := (cylinderNeighborhood X).obj V
  let L' := (cylinderNeighborhood X).obj U
  let j := ((cylinderNeighborhood X).map b).left
  let z := (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left
  let z' := (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj U) 0).left
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.additiveGroupObject (Spec (.of k))).left) :=
    IsAffine.of_isIso (AlgebraicGeometry.nativePolynomialAffineLineIso (.of k)).hom
  have : IsAffine L'.left := by
    change IsAffine (pullback (U.hom ≫ X.hom)
      ((SmoothSite.additiveGroupObject (Spec (.of k))).hom))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (show U.left ⟶ Spec (.of k) from U.hom ≫ X.hom)
      ((SmoothSite.additiveGroupObject (Spec (.of k))).hom)
  have : IsClosedImmersion z' := inferInstanceAs
    (IsClosedImmersion (SmoothSite.Contraction.nativeAffineSection
      (.of k) ((toSmoothSite X).obj U) 0).left)
  have hc : (b.left ≫ a) ≫ q.left = z' ≫ j := by
    rw [Category.assoc, H.w, Category.id_comp]
    exact (congrArg (fun f => f.left)
      (SmoothSite.Contraction.nativeAffineSection_naturality (.of k) ((toSmoothSite X).map b)
0)).symm
  let base : L.left ⟶ Spec (.of k) :=
    (SmoothSite.Contraction.affineLineCylinder.obj ((toSmoothSite X).obj V)).hom
  obtain ⟨E', hE', e₀, q₀, a', hq₀, hqc₀, hqs₀, he₀, ha', H'⟩ :=
    Scheme.Hom.exists_affine_whole_closed_refinement base q.left j z' (b.left ≫ a) hc
  let : Etale q₀ := hq₀
  let : QuasiCompact q₀ := hqc₀
  let : IsSeparated q₀ := hqs₀
  let N : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left :=
    MorphismProperty.Over.mk ⊤ (q₀ ≫ L'.hom) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have he : (e₀ ≫ e.left) ≫ W.hom = N.hom := by
    rw [Category.assoc, MorphismProperty.Over.w e, ← MorphismProperty.Over.w q,
      ← Category.assoc e₀, he₀, Category.assoc]
    change q₀ ≫ (((cylinderNeighborhood X).map b).left ≫ L.hom) = q₀ ≫ L'.hom
    rw [MorphismProperty.Over.w]
  let e' : N ⟶ W := MorphismProperty.Over.homMk (e₀ ≫ e.left) he
  let q' : N ⟶ L' := MorphismProperty.Over.homMk q₀ rfl
  have hcompat : z' ≫ L'.hom = U.hom ≫ z :=
    congrArg (fun f => f.left) (SmoothSite.Contraction.nativeAffineSection_naturality (.of k)
(toBase X U) 0)
  have haN : a' ≫ N.hom = U.hom ≫ z := by
    change a' ≫ (q₀ ≫ L'.hom) = _
    rw [← Category.assoc, H'.w, Category.id_comp, hcompat]
  let zU : U ⟶ (baseChange z).obj N := MorphismProperty.Over.homMk
    (pullback.lift a' U.hom haN) (pullback.lift_snd _ _ _)
  have hmf {A B : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left}
      (f : A ⟶ B) : ((baseChange z).map f).left ≫ pullback.fst B.hom z =
        pullback.fst A.hom z ≫ f.left := pullback.lift_fst _ _ _
  have hms {A B : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left}
      (f : A ⟶ B) : ((baseChange z).map f).left ≫ pullback.snd B.hom z =
        pullback.snd A.hom z := pullback.lift_snd _ _ _
  have hae : a ≫ e.left = v.left ≫ pullback.fst W.hom z := by
    rw [← haz, Category.assoc, ← hmf e, ← Category.assoc]
    exact congrArg (fun f => f.left ≫ pullback.fst W.hom z) hze
  refine ⟨U, v', inferInstance, inferInstance, hv', hw', N, e', q', a', zU,
    hE', hq₀, hqc₀, hqs₀, H', pullback.lift_fst _ _ _, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change zU.left ≫ ((baseChange z).map q').left = (zeroNeighborhoodLift X U).left
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, ← Category.assoc]
      change (pullback.lift a' U.hom haN ≫ pullback.fst N.hom z) ≫ q₀ = _
      rw [pullback.lift_fst]
      exact (H'.w.trans (Category.id_comp _)).trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hms]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  · apply MorphismProperty.Over.Hom.ext
    change zU.left ≫ ((baseChange z).map e').left = v'.left
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, ← Category.assoc]
      change (pullback.lift a' U.hom haN ≫ pullback.fst N.hom z) ≫ (e₀ ≫ e.left) = _
      rw [pullback.lift_fst, ← Category.assoc, ha', Category.assoc, hae]
      rfl
    · rw [Category.assoc, hms]
      exact (pullback.lift_snd _ _ _).trans (MorphismProperty.Over.w v').symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
