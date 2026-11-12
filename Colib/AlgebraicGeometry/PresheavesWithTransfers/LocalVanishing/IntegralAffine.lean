/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.OpenImage
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
# Integral-affine local vanishing and dense open restriction

An integral-affine local vanishing theorem yields zero neighborhoods for
restrictions to dense opens in every smooth scheme.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Coefficient.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `3b918a1a2a6881bfa0fbf84e0bbccfeb63e1b1d3`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

/-- The original integral-affine local-zero contract for arbitrary HI presheaves.
-/
def IntegralAffineLocalZero (k : Type u) [Field k] : Prop :=
  ∀ {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsIntegral X.left]
    [Nonempty A.left] (a : A ⟶ X) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{u + 1} k) (_hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (_hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left),
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0

variable {k : Type u} [Field k]

/-- The original dense-open restriction has affine zero neighborhoods from the input. -/
theorem exists_zero_neighborhood_of_dense_open_of_integralAffineLocalZero
    (hD : IntegralAffineLocalZero k)
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  let C := SmoothSite.integralAffineCover k X
  obtain ⟨i, t, ht⟩ := C.exists_eq x
  let T := SmoothSite.mk (C.f i ≫ X.hom)
  let f : T ⟶ X := SmoothSite.homMk (C.f i) rfl
  have : IsAffine T.left := inferInstanceAs (IsAffine (C.X i))
  have : IsIntegral T.left := inferInstanceAs (IsIntegral (C.X i))
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (C.f i))
  let B := SmoothSite.etalePullback a f
  let j : B ⟶ T := SmoothSite.etalePullbackSnd a f
  let b : B ⟶ A := SmoothSite.etalePullbackFst a f
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left f.left))
  have : Nonempty B.left := by
    obtain ⟨y, ⟨t', ht'⟩, hy⟩ := ha.inter_open_nonempty
      (Set.range f.left) f.left.isOpenEmbedding.isOpen_range ⟨f.left t, t, rfl⟩
    have hm : t' ∈ Set.range (pullback.snd a.left f.left) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change f.left t' ∈ Set.range a.left
      rwa [ht']
    obtain ⟨v, _⟩ := hm
    exact ⟨v⟩
  have hj : j ≫ f = b ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm
  have hv' : P.transfer ((Cor.graphFunctor k).map j)
      (P.transfer ((Cor.graphFunctor k).map f) v) = 0 := by
    have he := ConcreteCategory.congr_hom
      (congrArg P.transfer (congrArg (Cor.graphFunctor k).map hj)) v
    simpa only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply, hv, map_zero] using he
  obtain ⟨O, hO, htO, hz⟩ :=
    hD j P hP
      (P.transfer ((Cor.graphFunctor k).map f) v) hv' t
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ T.hom)
  let o : S ⟶ T := SmoothSite.homMk O.ι rfl
  let g := o ≫ f
  have : IsAffine S.left := hO
  have : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ C.f i))
  have hg : P.transfer ((Cor.graphFunctor k).map g) v = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hz
  refine ⟨g.left.opensRange, isAffineOpen_opensRange g.left, ?_,
    P.zero_on_open_image_general g v hg⟩
  exact ⟨⟨t, htO⟩, ht⟩

end AlgebraicGeometry.PresheafWithTransfers
