/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback

/-! # Restricting the entire polynomial endpoint to an original open chart -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber
open Stacks.Chow

/-- Original open immersions preserve the fundamental coefficient at every point. -/
theorem fundamentalCycle_apply_openImmersion {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (i : X ⟶ Y) [IsOpenImmersion i] (x : X) :
    fundamentalCycle X x = fundamentalCycle Y (i x) := by
  let e := (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
  have hg : i x ∈ genericPoints Y ↔ x ∈ genericPoints X := by
    rw [← ringKrullDim_stalk_eq_zero_iff_mem_genericPoints Y (i x),
      ← ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x, ringKrullDim_eq_of_ringEquiv e]
  by_cases hx : x ∈ genericPoints X
  · rw [fundamentalCycle_apply_generic X ⟨x, hx⟩,
      fundamentalCycle_apply_generic Y ⟨i x, hg.mpr hx⟩]
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Module.length_eq_of_ringEquiv e).symm
  · rw [fundamentalCycle_apply_of_notMem X x hx,
      fundamentalCycle_apply_of_notMem Y (i x) (mt hg.mp hx)]

/-- A Cartesian restriction of a closed support preserves its full coefficient
at every point of the original open chart. -/
theorem fundamentalCycle_pushforward_cartesian_open_apply
    {A B C D : Scheme.{u}} [IsNoetherian A] [IsNoetherian C]
    (p : A ⟶ B) (i : A ⟶ C) (j : B ⟶ D) (q : C ⟶ D)
    [IsClosedImmersion p] [IsClosedImmersion q] [IsOpenImmersion j]
    (H : IsPullback p i j q) (x : B) :
    finiteCyclePushforward p (fundamentalCycle A) x =
      finiteCyclePushforward q (fundamentalCycle C) (j x) := by
  let : IsOpenImmersion i := MorphismProperty.of_isPullback H inferInstance
  by_cases h : j x ∈ Set.range q
  · obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback H x y hy.symm
    have hh : j (p z) = q (i z) := congrArg (fun f : A ⟶ D => f z) H.w
    rw [← hz, hh, finiteCyclePushforward_apply_of_isClosedImmersion,
      finiteCyclePushforward_apply_of_isClosedImmersion]
    exact fundamentalCycle_apply_openImmersion i z
  · have hp : x ∉ Set.range p := by
      rintro ⟨z, hz⟩
      exact h ⟨i z, (congrArg (fun f : A ⟶ D => f z) H.w).symm.trans (congrArg j hz)⟩
    rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range _ _ hp,
      finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range _ _ h]

section Component

variable {k : Type u} [Field k] {D E : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ D)

/-- The ideal of the whole component fiber is the actual base-change ideal. -/
theorem fiberMap_ker [IsClosedImmersion j] :
    (fiberMap f a j).ker = j.ker.comap (inclusion f a) := by
  rw [← (fiberMap_isPullback f a j).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

variable [IsNoetherian D] [IsNoetherian E] [IsOpenImmersion j]

/-- The coefficient of a component endpoint on the original open chart
preserves the full reduced-component and fiber maps. -/
theorem polynomialComponentEndpoint_open_apply (z : E) (x : fiber (j ≫ f) a) :
    polynomialComponentEndpoint (j ≫ f) a z x =
      polynomialComponentEndpoint f a (j z) (fiberMap f a j x) := by
  let u := (integralComponentAt z).subschemeι
  let v := (integralComponentAt (j z)).subschemeι
  let e := integralComponentMap j z
  have he : e ≫ v = u ≫ j := integralComponentMap_subschemeι j z
  have hfamily : (u ≫ (j ≫ f)) ≫ 𝟙 _ = e ≫ (v ≫ f) := by
    rw [Category.comp_id, ← Category.assoc e v f, he, Category.assoc]
  let w := pullback.map (point a) (u ≫ (j ≫ f)) (point a) (v ≫ f)
    (𝟙 _) e (𝟙 _) (by simp) hfamily
  have hw₀ : w ≫ pullback.fst (point a) (v ≫ f) =
      pullback.fst (point a) (u ≫ (j ≫ f)) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hw₁ : w ≫ inclusion (v ≫ f) a = inclusion (u ≫ (j ≫ f)) a ≫ e :=
    pullback.lift_snd _ _ _
  have hcomp := (fiberMap_comp_of_square f a j u v e w hw₀ hw₁ he).symm
  have hker : (fiberMap f a v).ker.comap (fiberMap f a j) =
      (fiberMap (j ≫ f) a u).ker := by
    rw [fiberMap_ker, fiberMap_ker, ← Scheme.IdealSheafData.comap_comp,
      fiberMap_inclusion, Scheme.IdealSheafData.comap_comp]
    have hv : v.ker.comap j = u.ker := by
      dsimp only [u, v]
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
      exact comap_integralComponentAt_of_isOpenImmersion j z
    rw [hv]
  have H := isPullback_of_isClosedImmersion _ _ _ _ hcomp hker
  let : IsOpenImmersion (fiberMap f a j) :=
    MorphismProperty.of_isPullback (fiberMap_isPullback f a j).flip inferInstance
  let : IsNoetherian (integralComponentAt z).subscheme := isNoetherian_of_finiteType u
  let : IsNoetherian (integralComponentAt (j z)).subscheme := isNoetherian_of_finiteType v
  exact fundamentalCycle_pushforward_cartesian_open_apply _ _ _ _ H x

omit [IsNoetherian E] in
/-- A prime outside the chart contributes zero to each chart endpoint point. -/
theorem polynomialComponentEndpoint_open_eq_zero (z : D) (hz : z ∉ Set.range j)
    (x : fiber (j ≫ f) a) :
    polynomialComponentEndpoint f a z (fiberMap f a j x) = 0 := by
  let i := (integralComponentAt z).subschemeι
  let : IsNoetherian (integralComponentAt z).subscheme := isNoetherian_of_finiteType i
  by_contra h
  change finiteCyclePushforward (fiberMap f a i)
    (fundamentalCycle (fiber (i ≫ f) a)) (fiberMap f a j x) ≠ 0 at h
  obtain ⟨y, _, hy⟩ := finiteCyclePushforward_support_subset _ _ h
  have h₁ := congrArg (fun g : fiber (i ≫ f) a ⟶ D => g y) (fiberMap_inclusion f a i)
  have h₂ := congrArg (fun g : fiber (j ≫ f) a ⟶ D => g x) (fiberMap_inclusion f a j)
  have h₃ : j (inclusion (j ≫ f) a x) ∈ Set.range i :=
    ⟨inclusion (i ≫ f) a y, h₁.symm.trans ((congrArg (inclusion f a) hy).trans h₂)⟩
  change j (inclusion (j ≫ f) a x) ∈ Set.range (integralComponentAt z).subschemeι at h₃
  rw [(integralComponentAt z).range_subschemeι, coe_support_integralComponentAt] at h₃
  exact hz ((specializes_iff_mem_closure.mpr h₃).mem_open
    j.isOpenEmbedding.isOpen_range (Set.mem_range_self _))

/-- A cycle with the restricted coefficients specializes to the restricted
whole endpoint coefficient. -/
theorem polynomialEndpointMap_open_apply (c : AlgebraicCycle D ℤ)
    (d : AlgebraicCycle E ℤ) (h : ∀ z : E, d z = c (j z))
    (x : fiber (j ≫ f) a) :
    polynomialEndpointMap (j ≫ f) a d x = polynomialEndpointMap f a c (fiberMap f a j x) := by
  classical
  rw [polynomialEndpointMap_apply_coeff, polynomialEndpointMap_apply_coeff]
  let s := Function.locallyFinsupp.finite_support c
  let t := Function.locallyFinsupp.finite_support d
  let w (z : D) := c z * polynomialComponentEndpoint f a z (fiberMap f a j x)
  let I := t.toFinset.image (⇑j)
  have hI : I ⊆ s.toFinset := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hy' : d y ≠ 0 := t.mem_toFinset.mp hy
    apply s.mem_toFinset.mpr
    change c (j y) ≠ 0
    rw [← h y]
    exact hy'
  calc
    _ = ∑ z ∈ t.toFinset, w (j z) := by
      apply Finset.sum_congr rfl
      intro z _
      change d z * polynomialComponentEndpoint (j ≫ f) a z x =
        c (j z) * polynomialComponentEndpoint f a (j z) (fiberMap f a j x)
      rw [h z, polynomialComponentEndpoint_open_apply]
    _ = ∑ z ∈ I, w z :=
      (Finset.sum_image (fun _ _ _ _ h' => j.isOpenEmbedding.injective h')).symm
    _ = ∑ z ∈ s.toFinset, w z := by
      apply Finset.sum_subset hI
      intro z hz hzI
      have hn : z ∉ Set.range j := by
        rintro ⟨y, rfl⟩
        have hy : d y ≠ 0 := (h y).symm ▸ (s.mem_toFinset.mp hz : c (j y) ≠ 0)
        exact hzI (Finset.mem_image.mpr ⟨y, t.mem_toFinset.mpr hy, rfl⟩)
      change c z * polynomialComponentEndpoint f a z (fiberMap f a j x) = 0
      rw [polynomialComponentEndpoint_open_eq_zero f a j z hn, mul_zero]

/-- The same comparison for a specified polynomial parameter on the chart. -/
theorem polynomialEndpointMap_open_apply_of_comp_eq (f' : E ⟶ Spec (.of (Polynomial k)))
    (hf' : j ≫ f = f') (c : AlgebraicCycle D ℤ) (d : AlgebraicCycle E ℤ)
    (h : ∀ z : E, d z = c (j z)) (x : fiber f' a) :
    polynomialEndpointMap f' a d x = polynomialEndpointMap f a c
      (pullback.map (point a) f' (point a) f (𝟙 _) j (𝟙 _) (by simp)
        ((Category.comp_id _).trans hf'.symm) x) := by
  subst f'
  exact polynomialEndpointMap_open_apply f a j c d h x

end Component

end AlgebraicGeometry.AlgebraicCycle
