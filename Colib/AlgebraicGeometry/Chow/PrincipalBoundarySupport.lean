/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.ProperQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Actual finite supports of a boundary-unit principal cycle

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Boundary/NeighborhoodComplement.lean`
and `Motivic/Aglib/AlgebraicGeometry/Cycles/Divisors/PrincipalOrder.lean` in the 2026-10-21
source checkpoint. Unlike that source, the cycle here is native `Stacks.Chow.principalCycle`,
not a Finsupp replacement. Properness and the quasi-affine retained open prove finiteness
of every actual integral support. Component dominance and endpoint intersection multiplicities
are separate obligations, not hypotheses disguised as a principal-family construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

variable {C V S : Scheme.{u}} [IsIntegral C] [IsNoetherian C]

/-- The entire closure of each nonzero principal coefficient avoids the unit open. -/
theorem principalCycle_closure_subset_retained
    (j : V ⟶ C) (U : C.Opens) [Nonempty U]
    (hU : (Set.range j)ᶜ ⊆ (U : Set C)) (f : Γ(C, U)) (hf : IsUnit f)
    (x : C) (hx : principalCycle C (C.germToFunctionField U f) x ≠ 0) :
    closure ({x} : Set C) ⊆ Set.range j := by
  have hxU : x ∉ U := fun hm => hx (C.ord_of_isUnit hf hm)
  have hc : closure ({x} : Set C) ⊆ (U : Set C)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hxU) U.isOpen.isClosed_compl
  intro y hy
  by_contra hn
  exact hc hy (hU hn)

/-- Finiteness of each native integral support is a conclusion of properness and
boundary avoidance, not an input about the cycle. -/
theorem principalCycle_support_isFinite [IsAffine S] [V.IsQuasiAffine]
    (q : C ⟶ S) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
    (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
    (f : Γ(C, U)) (hf : IsUnit f) (x : C)
    (hx : principalCycle C (C.germToFunctionField U f) x ≠ 0) :
    IsFinite ((integralComponentAt x).subschemeι ≫ q) := by
  apply Scheme.isFinite_closed_support_in_quasiAffine_open q j
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  exact principalCycle_closure_subset_retained j U hU f hf x hx

end Stacks.Chow
