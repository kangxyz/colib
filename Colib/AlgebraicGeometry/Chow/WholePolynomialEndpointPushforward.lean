/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree

/-! # Pushforward of whole polynomial endpoint cycles -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.AffineLineFiber Stacks.Chow

/-- Finite pushforward depends on the actual map. -/
theorem finiteCyclePushforward_congr {X Y : Scheme.{u}} (f g : X ⟶ Y)
    [IsFinite f] [IsFinite g] (h : f = g) :
    finiteCyclePushforward f = finiteCyclePushforward g := by
  subst g
  rfl

section ClosedImmersion

variable {k : Type u} [Field k] {D E : Scheme.{u}} [IsNoetherian D] [IsNoetherian E]
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ D) [IsClosedImmersion j]

omit [IsNoetherian D] [IsNoetherian E] in
/-- The reduced closure of a point maps isomorphically onto the reduced
closure of its actual image under a closed immersion. -/
theorem integralComponentMap_isIso_of_isClosedImmersion (z : E) :
    IsIso (integralComponentMap j z) := by
  let l := integralComponentMap j z
  let i := (integralComponentAt (j z)).subschemeι
  have hi : IsClosedImmersion (l ≫ i) := by
    change IsClosedImmersion (integralComponentMap j z ≫ (integralComponentAt (j z)).subschemeι)
    rw [integralComponentMap_subschemeι]
    infer_instance
  let : IsClosedImmersion (l ≫ i) := hi
  let : IsClosedImmersion l := IsClosedImmersion.of_comp l i
  let : Surjective l := Surjective.of_universallyClosed_of_isDominant l
  let : IsIntegral (integralComponentAt (j z)).subscheme := isIntegral_integralComponentAt _
  exact isIso_of_isClosedImmersion_of_surjective l

/-- Specializing the reduced closure of the image of a point along a closed
immersion pushes the entire component fiber to that same endpoint. -/
theorem polynomialComponentEndpoint_closed_image (z : E) :
    polynomialComponentEndpoint f a (j z) =
      finiteCyclePushforward (fiberMap f a j) (polynomialComponentEndpoint (j ≫ f) a z) := by
  let u := (integralComponentAt z).subschemeι
  let v := (integralComponentAt (j z)).subschemeι
  let e := integralComponentMap j z
  let : IsIso e := integralComponentMap_isIso_of_isClosedImmersion j z
  let : IsNoetherian (integralComponentAt z).subscheme :=
    isNoetherian_of_finiteType_of_isNoetherian u
  let : IsNoetherian (integralComponentAt (j z)).subscheme :=
    isNoetherian_of_finiteType_of_isNoetherian v
  have he : e ≫ v = u ≫ j := integralComponentMap_subschemeι j z
  have hfamily : (u ≫ (j ≫ f)) ≫ 𝟙 _ = e ≫ (v ≫ f) := by
    rw [Category.comp_id, ← Category.assoc e v f, he, Category.assoc]
  let w := pullback.map (point a) (u ≫ (j ≫ f)) (point a) (v ≫ f)
    (𝟙 _) e (𝟙 _) (by simp) hfamily
  have hw : IsIso w := inferInstanceAs (IsIso
    (pullback.map (point a) (u ≫ (j ≫ f)) (point a) (v ≫ f)
      (𝟙 _) e (𝟙 _) _ hfamily))
  let : IsIso w := hw
  have hw₀ : w ≫ pullback.fst (point a) (v ≫ f) =
      pullback.fst (point a) (u ≫ (j ≫ f)) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hw₁ : w ≫ inclusion (v ≫ f) a = inclusion (u ≫ (j ≫ f)) a ≫ e :=
    pullback.lift_snd _ _ _
  have hcomp := fiberMap_comp_of_square f a j u v e w hw₀ hw₁ he
  change finiteCyclePushforward (fiberMap f a v) (fundamentalCycle (fiber (v ≫ f) a)) =
    finiteCyclePushforward (fiberMap f a j)
      (finiteCyclePushforward (fiberMap (j ≫ f) a u)
        (fundamentalCycle (fiber (u ≫ (j ≫ f)) a)))
  rw [← finiteCyclePushforward_fundamentalCycle_iso (asIso w),
    finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply]
  exact DFunLike.congr_fun (finiteCyclePushforward_congr _ _
    ((congrArg (· ≫ fiberMap f a v) (asIso_hom w)).trans hcomp)) _

/-- Whole endpoint specialization commutes with the original closed pushforward. -/
theorem polynomialEndpointMap_pushforward_closed (c : AlgebraicCycle E ℤ) :
    polynomialEndpointMap f a (finiteCyclePushforward j c) =
      finiteCyclePushforward (fiberMap f a j) (polynomialEndpointMap (j ≫ f) a c) := by
  classical
  have hc := sum_apply_smul_single_eq_self_on_univ (Function.locallyFinsupp.finite_support c)
  rw [← hc]
  simp only [map_sum, finiteCyclePushforward_single_of_isClosedImmersion,
    polynomialEndpointMap_single, polynomialComponentEndpoint_closed_image, map_zsmul]

end ClosedImmersion

section Regular

variable {k : Type u} [Field k] {D : Scheme.{u}} [IsNoetherian D]
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k)

/-- At a generic point of a regular endpoint cut, the weighted component sum
recovers the multiplicity of the whole fiber. -/
theorem polynomialEndpointMap_fundamentalCycle_apply_of_regular
    (x : genericPoints (fiber f a))
    (hreg : IsSMulRegular (D.presheaf.stalk (inclusion f a x.val))
      (scalar f a (inclusion f a x.val))) :
    polynomialEndpointMap f a (fundamentalCycle D) x.val =
      fundamentalCycle (fiber f a) x.val := by
  classical
  let h := fundamentalCycle_genericPoints_finite D
  let : Fintype (genericPoints D) := h.fintype
  let c := fundamentalCycle D
  let s := Function.locallyFinsupp.finite_support c
  let d (z : D) := single z (c z)
  have hsc : s.toFinset ⊆ h.toFinset := fun z hz =>
    h.mem_toFinset.mpr (support_fundamentalCycle_subset D (s.mem_toFinset.mp hz))
  have hs : (∑ z ∈ s.toFinset, d z) = ∑ z ∈ h.toFinset, d z := by
    apply Finset.sum_subset hsc
    intro z _ hz
    have he : c z = 0 := Function.notMem_support.mp (fun hz' => hz (s.mem_toFinset.mpr hz'))
    change single z (c z) = 0
    rw [he, single_zero]
  have hd : (∑ z : genericPoints D, d z.val) = c :=
    (Finset.sum_subtype h.toFinset (fun z => h.mem_toFinset) d).symm.trans
      (hs.symm.trans (sum_apply_smul_single_eq_self_on_univ s))
  let : ∀ z : genericPoints D, IsNoetherian (integralComponentAt z.val).subscheme :=
    fun z => isNoetherian_of_finiteType_of_isNoetherian (integralComponentAt z.val).subschemeι
  rw [show fundamentalCycle D = c from rfl, ← hd]
  simp only [d, map_sum, polynomialEndpointMap_single, coe_sum, Finset.sum_apply,
    coe_zsmul, Pi.smul_apply]
  simp only [c, fundamentalCycle_apply_generic, zsmul_eq_mul, Int.cast_id]
  simpa only [polynomialComponentEndpoint, fundamentalCycle_apply_generic] using
    (fundamentalCycle_apply_eq_sum_componentFibers_of_regular f a x hreg).symm

end Regular

end AlgebraicGeometry.AlgebraicCycle
