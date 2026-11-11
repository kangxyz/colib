/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.AffineLineFiberMultiplicity
public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.IntersectionIdeal
public import StacksFrontier.Topology.Sober.Generization

/-!
# Whole endpoint coefficients as the actual original component-fiber sum

At a generic point of the full endpoint, the literal component-fiber maps are
finite closed immersions. Any preimage is therefore generic in that component
fiber. Their coefficients are the lengths of the actual ambient quotients by
`t - a` plus the original reduced-component ideal. The local devissage theorem
thus gives the finite sum over every original generic component, with all
original multiplicities, including zero contributions away from a component.

Only equality at generic points of the full fiber is asserted here. The global
correspondence application supplies vanishing away from generic source points
from actual admissibility, rather than assuming a false ungraded formula for
arbitrary flat A1 families of mixed dimension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.AffineLineFiber

open Stacks.Chow

variable {k : Type u} [Field k] {D E : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ D)

/-- The canonical map between the two full parameter fibers. -/
def fiberMap : fiber (j ≫ f) a ⟶ fiber f a :=
  pullback.map _ _ _ _ (𝟙 _) j (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)] theorem fiberMap_inclusion :
    fiberMap f a j ≫ inclusion f a = inclusion (j ≫ f) a ≫ j := by
  simp [fiberMap, inclusion, pullback.map]

/-- The component endpoint is the actual Cartesian intersection. -/
theorem fiberMap_isPullback :
    IsPullback (fiberMap f a j) (inclusion (j ≫ f) a) (inclusion f a) j := by
  have H : IsPullback (fiberMap f a j ≫ pullback.fst (point a) f)
      (inclusion (j ≫ f) a) (point a) (j ≫ f) := by
    simpa [fiberMap, pullback.map, inclusion] using
      IsPullback.of_hasPullback (point a) (j ≫ f)
  exact H.of_right (fiberMap_inclusion f a j) (IsPullback.of_hasPullback (point a) f)

instance fiberMap_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (fiberMap f a j) :=
  MorphismProperty.of_isPullback (fiberMap_isPullback f a j).flip inferInstance

/-- The full intersection ideal is the exact sum, not its radical. -/
theorem fiberMap_composite_stalk [IsClosedImmersion j] (x : D) :
    IdealSheafData.stalk (fiberMap f a j ≫ inclusion f a).ker x =
      Ideal.span {scalar f a x} ⊔ IdealSheafData.stalk j.ker x := by
  rw [Scheme.Hom.ker_comp_eq_sup_of_isPullback _ _ _ _ (fiberMap_isPullback f a j),
    AlgebraicGeometry.IdealSheafData.stalk_sup, inclusion_stalk]

/-- Over a generic whole-fiber point, the component-fiber coefficient is the
actual original ambient quotient length. -/
theorem fiberMap_fundamentalCycle_apply [IsNoetherian E] [IsClosedImmersion j]
    (x : genericPoints (fiber f a)) :
    finiteCyclePushforward (fiberMap f a j) (AlgebraicCycle.fundamentalCycle (fiber (j ≫ f) a))
        x.val =
      ((Module.length (D.presheaf.stalk (inclusion f a x.val))
        (D.presheaf.stalk (inclusion f a x.val) ⧸
          (Ideal.span {scalar f a (inclusion f a x.val)} ⊔
            IdealSheafData.stalk j.ker (inclusion f a x.val)))).toNat : ℤ) := by
  classical
  let l := fiberMap f a j ≫ inclusion f a
  suffices h : finiteCyclePushforward (fiberMap f a j)
      (AlgebraicCycle.fundamentalCycle (fiber (j ≫ f) a)) x.val =
        ((closedImmersionQuotientStalkLength l (inclusion f a x.val)).toNat : ℤ) by
    simpa only [closedImmersionQuotientStalkLength, l, fiberMap_composite_stalk] using h
  by_cases hx : x.val ∈ Set.range (fiberMap f a j)
  · obtain ⟨e, he⟩ := hx
    have hegen := mem_genericPoints_of_isFinite_image (fiberMap f a j) e (by simpa only [he] using x.property)
    rw [← he, finiteCyclePushforward_apply_of_isClosedImmersion,
      AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨e, hegen⟩]
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (closedImmersionQuotientStalkLength_image l e).symm
  · have hl : inclusion f a x.val ∉ Set.range l := by
      rintro ⟨e, he⟩
      exact hx ⟨e, (inclusion f a).isClosedEmbedding.injective he⟩
    rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range _ _ hx,
      closedImmersionQuotientStalkLength_eq_zero_of_notMem_range l _ hl]
    simp

/-- The local whole-fiber coefficient, indexed by every original generic
component, with its original stalk-length weight. -/
theorem fundamentalCycle_apply_eq_sum_componentFibers
    [IsNoetherian D] [Flat f] [Fintype (genericPoints D)]
    [∀ z : genericPoints D, IsNoetherian (integralComponentAt z.val).subscheme]
    (x : genericPoints (fiber f a)) :
    AlgebraicCycle.fundamentalCycle (fiber f a) x.val =
      ∑ z : genericPoints D,
        ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) *
          finiteCyclePushforward (fiberMap f a (integralComponentAt z.val).subschemeι)
            (AlgebraicCycle.fundamentalCycle
              (fiber ((integralComponentAt z.val).subschemeι ≫ f) a)) x.val := by
  classical
  rw [fundamentalCycle_apply_eq_finsum_componentsThrough]
  simp_rw [fiberMap_fundamentalCycle_apply, Scheme.IdealSheafData.ker_subschemeι]
  let c (z : D) : ℤ :=
    ((Module.length (D.presheaf.stalk z) (D.presheaf.stalk z)).toNat : ℤ) *
      ((Module.length (D.presheaf.stalk (inclusion f a x.val))
        (D.presheaf.stalk (inclusion f a x.val) ⧸
          (Ideal.span {scalar f a (inclusion f a x.val)} ⊔
            IdealSheafData.stalk (integralComponentAt z) (inclusion f a x.val)))).toNat : ℤ)
  let hfin := AlgebraicCycle.fundamentalCycle_genericPoints_finite D
  trans ∑ z ∈ hfin.toFinset, c z
  · apply finsum_cond_eq_sum_of_cond_iff c
    intro z hz
    constructor
    · intro h
      exact hfin.mem_toFinset.mpr (mem_genericPoints_of_forall_specializes_eq h.2)
    · intro h
      refine ⟨?_, forall_specializes_eq_of_mem_genericPoints (hfin.mem_toFinset.mp h)⟩
      by_contra hs
      have hnot : inclusion f a x.val ∉ (integralComponentAt z).support := by
        rw [← SetLike.mem_coe, coe_support_integralComponentAt]
        exact fun hmem => hs (specializes_iff_mem_closure.mpr hmem)
      have htop := (Stacks.Divisors.stalk_eq_top_iff_notMem_support
        (integralComponentAt z) (inclusion f a x.val)).mpr hnot
      apply hz
      simp only [c, htop, sup_top_eq, Module.length_eq_zero, ENat.toNat_zero,
        Nat.cast_zero, mul_zero]
  · exact Finset.sum_subtype hfin.toFinset (fun z => hfin.mem_toFinset) c

end AlgebraicGeometry.Scheme.AffineLineFiber
