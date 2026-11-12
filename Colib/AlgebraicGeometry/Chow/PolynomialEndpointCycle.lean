/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.AffineLineFiberComponentCoefficient
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-! # Full polynomial endpoint cycles

Each nonzero coefficient acts on the fundamental cycle of the whole fiber
of the corresponding integral support. The map is additive on the original
native cycle group, with every scheme-theoretic fiber multiplicity retained.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Cycles/PrincipalDivisor/Faces/`
`WholeComponentFiber.lean` at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineLineFiber

section Maps

variable {k : Type u} [Field k] {D E A B : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k)

/-- The induced map of whole fibers preserves the original scalar point projection. -/
theorem fiberMap_fst (j : E ⟶ D) :
    fiberMap f a j ≫ pullback.fst (point a) f = pullback.fst (point a) (j ≫ f) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The two actual component-fiber maps commute with the given scheme maps. -/
theorem fiberMap_comp_of_square (j : E ⟶ D) (u : A ⟶ E) (v : B ⟶ D) (e : A ⟶ B)
    (w : fiber (u ≫ (j ≫ f)) a ⟶ fiber (v ≫ f) a)
    (hw₀ : w ≫ pullback.fst (point a) (v ≫ f) = pullback.fst (point a) (u ≫ (j ≫ f)))
    (hw₁ : w ≫ inclusion (v ≫ f) a = inclusion (u ≫ (j ≫ f)) a ≫ e)
    (he : e ≫ v = u ≫ j) :
    w ≫ fiberMap f a v = fiberMap (j ≫ f) a u ≫ fiberMap f a j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fiberMap_fst, hw₀]
  · change (w ≫ fiberMap f a v) ≫ inclusion f a =
      (fiberMap (j ≫ f) a u ≫ fiberMap f a j) ≫ inclusion f a
    simp only [Category.assoc, fiberMap_inclusion, fiberMap_inclusion_assoc]
    rw [← Category.assoc w, hw₁, Category.assoc, he]

end Maps

/-- A stalk with finite self-length belongs to a generic point. -/
theorem mem_genericPoints_of_stalk_length_ne_top {E : Scheme.{u}} (y : E)
    (h : Module.length (E.presheaf.stalk y) (E.presheaf.stalk y) ≠ ⊤) :
    y ∈ genericPoints E := by
  let : IsArtinianRing (E.presheaf.stalk y) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h)).2
  let : Ring.KrullDimLE 0 (E.presheaf.stalk y) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  exact (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints E y).mp
    (ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance)

section ClosedSupport

variable {D E : Scheme.{u}} [IsNoetherian E] (i : E ⟶ D) [IsClosedImmersion i]

/-- At a point whose preimage consists of generic points, the whole closed
support contributes the length of its actual quotient stalk. -/
theorem fundamentalCycle_pushforward_closed_apply (x : D)
    (hx : ∀ y : E, i y = x → y ∈ genericPoints E) :
    finiteCyclePushforward i (fundamentalCycle E) x =
      ((closedImmersionQuotientStalkLength i x).toNat : ℤ) := by
  by_cases h : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := h
    rw [finiteCyclePushforward_apply_of_isClosedImmersion,
      fundamentalCycle_apply_generic _ ⟨y, hx y rfl⟩]
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (closedImmersionQuotientStalkLength_image i y).symm
  · rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range _ _ h,
      closedImmersionQuotientStalkLength_eq_zero_of_notMem_range i _ h]
    rfl

/-- A closed support contributes zero at any point with no generic preimage. -/
theorem fundamentalCycle_pushforward_closed_eq_zero (x : D)
    (hx : ∀ y : E, i y = x → y ∉ genericPoints E) :
    finiteCyclePushforward i (fundamentalCycle E) x = 0 := by
  by_cases h : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := h
    rw [finiteCyclePushforward_apply_of_isClosedImmersion]
    exact fundamentalCycle_apply_of_notMem E y (hx y rfl)
  · exact finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range i x h

end ClosedSupport

section Intersection

variable {k : Type u} [Field k] {D E : Scheme.{u}} [IsNoetherian E]
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ D) [IsClosedImmersion j]

/-- At a finite-length double cut, every preimage is generic in the original
component fiber, so the full endpoint coefficient is its quotient colength. -/
theorem fiberMap_fundamentalCycle_apply_of_length_ne_top (x : fiber f a)
    (h : closedImmersionQuotientStalkLength (fiberMap f a j ≫ inclusion f a)
      (inclusion f a x) ≠ ⊤) :
    finiteCyclePushforward (fiberMap f a j) (fundamentalCycle (fiber (j ≫ f) a)) x =
      ((closedImmersionQuotientStalkLength (fiberMap f a j ≫ inclusion f a)
        (inclusion f a x)).toNat : ℤ) := by
  let e := fiberMap f a j
  let l := e ≫ inclusion f a
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    change closedImmersionQuotientStalkLength l (l y) ≠ ⊤ at h
    rw [closedImmersionQuotientStalkLength_image] at h
    have hg := mem_genericPoints_of_stalk_length_ne_top y h
    change finiteCyclePushforward e (fundamentalCycle (fiber (j ≫ f) a)) (e y) =
      ((closedImmersionQuotientStalkLength l (l y)).toNat : ℤ)
    rw [finiteCyclePushforward_apply_of_isClosedImmersion, closedImmersionQuotientStalkLength_image,
      fundamentalCycle_apply_generic _ ⟨y, hg⟩]
  · have hl : inclusion f a x ∉ Set.range l := by
      rintro ⟨y, hy⟩
      exact hx ⟨y, (inclusion f a).isClosedEmbedding.injective hy⟩
    rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range e _ hx,
      closedImmersionQuotientStalkLength_eq_zero_of_notMem_range l _ hl]
    rfl

end Intersection

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsNoetherian P]
  (f : P ⟶ Spec (.of (Polynomial k))) (a : k)

/-- The whole endpoint of the integral closed support of an original point. -/
def polynomialComponentEndpoint (z : P) : AlgebraicCycle (fiber f a) ℤ := by
  let i := (integralComponentAt z).subschemeι
  let : IsNoetherian (fiber (i ≫ f) a) := isNoetherian_of_finiteType (inclusion (i ≫ f) a ≫ i)
  exact finiteCyclePushforward (fiberMap f a i) (fundamentalCycle (fiber (i ≫ f) a))

/-- Intersect each closed component with the same full polynomial endpoint. -/
def polynomialEndpointMap : AlgebraicCycle P ℤ →+ AlgebraicCycle (fiber f a) ℤ := by
  classical
  let s (c : AlgebraicCycle P ℤ) := (Function.locallyFinsupp.finite_support c).toFinset
  refine
    { toFun := fun c => ∑ z ∈ s c, c z • polynomialComponentEndpoint f a z
      map_zero' := ?_
      map_add' := ?_ }
  · have h : s 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h := (Function.locallyFinsupp.finite_support (0 : AlgebraicCycle P ℤ)).mem_toFinset.mp hz
      exact h rfl
    rw [h, Finset.sum_empty]
  · intro c d
    let T := s c ∪ s d
    have hT : s (c + d) ⊆ T := by
      intro z hz
      by_contra hn
      have hc : c z = 0 := by
        by_contra h
        exact hn (Finset.mem_union_left _
          ((Function.locallyFinsupp.finite_support c).mem_toFinset.mpr h))
      have hd : d z = 0 := by
        by_contra h
        exact hn (Finset.mem_union_right _
          ((Function.locallyFinsupp.finite_support d).mem_toFinset.mpr h))
      have h := (Function.locallyFinsupp.finite_support (c + d)).mem_toFinset.mp hz
      exact h (by change c z + d z = 0; rw [hc, hd, add_zero])
    have hsum (c₀ : AlgebraicCycle P ℤ) (hc₀ : s c₀ ⊆ T) :
        (∑ z ∈ s c₀, c₀ z • polynomialComponentEndpoint f a z) =
          ∑ z ∈ T, c₀ z • polynomialComponentEndpoint f a z := by
      apply Finset.sum_subset hc₀
      intro z _ hz
      have he : c₀ z = 0 := by
        by_contra h
        exact hz ((Function.locallyFinsupp.finite_support c₀).mem_toFinset.mpr h)
      rw [he, zero_smul]
    rw [hsum (c + d) hT, hsum c Finset.subset_union_left, hsum d Finset.subset_union_right]
    simp only [coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The native endpoint coefficient sums over the actual cycle support. -/
theorem polynomialEndpointMap_apply_coeff (c : AlgebraicCycle P ℤ) (x : fiber f a) :
    polynomialEndpointMap f a c x =
      ∑ z ∈ (Function.locallyFinsupp.finite_support c).toFinset,
        c z * polynomialComponentEndpoint f a z x := by
  classical
  change ((∑ z ∈ (Function.locallyFinsupp.finite_support c).toFinset,
    c z • polynomialComponentEndpoint f a z) : AlgebraicCycle (fiber f a) ℤ) x = _
  simp only [coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro z _
  exact zsmul_eq_mul _ _

/-- The endpoint of a single prime uses its actual complete component fiber. -/
theorem polynomialEndpointMap_single [DecidableEq P] (z : P) (n : ℤ) :
    polynomialEndpointMap f a (single z n) = n • polynomialComponentEndpoint f a z := by
  by_cases hn : n = 0
  · simp only [hn, single_zero, map_zero, zero_smul]
  let h := Function.locallyFinsupp.finite_support (single z n : AlgebraicCycle P ℤ)
  have hset : h.toFinset = {z} := by
    ext y
    rw [h.mem_toFinset, Function.mem_support, single_apply, Finset.mem_singleton]
    split <;> simp_all
  change (∑ y ∈ h.toFinset, single z n y • polynomialComponentEndpoint f a y) = _
  rw [hset, Finset.sum_singleton, single_apply, ite_eq_left (rfl : z = z)]

end AlgebraicGeometry.AlgebraicCycle
