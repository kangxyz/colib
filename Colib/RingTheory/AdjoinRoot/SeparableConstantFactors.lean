/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TensorSwap
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Squarefree finite places after a separable constant extension

The closed point polynomial may be inseparable. The whole tensor-swap equivalence
identifies its scalar quotient with the scalar quotient of the separable constant
polynomial. Reducedness of the latter proves squarefreeness of the former. Thus
all actual upper point multiplicities are one without linearizing the closed point.
No characteristic or normality hypothesis, and no Milnor K-theory, is used.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

/-- An arbitrary irreducible point stays squarefree after extension by a separable
simple constant field. Inseparability of the point itself is allowed. -/
theorem squarefree_map_of_separable_constant (hp : p.Separable) :
    Squarefree (h.map (algebraMap k (AdjoinRoot p))) := by
  let : IsReduced (AdjoinRoot (p.map (algebraMap k (AdjoinRoot h)))) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (isRadical_iff_span_singleton.mp hp.map.squarefree.isRadical)
  have hred : IsReduced (AdjoinRoot (h.map (algebraMap k (AdjoinRoot p)))) :=
    isReduced_of_injective (tensorSwapEquiv p h).toRingHom
      (tensorSwapEquiv p h).injective
  have hrad : (Ideal.span
      ({h.map (algebraMap k (AdjoinRoot p))} : Set (AdjoinRoot p)[X])).IsRadical := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mpr
    change IsReduced (AdjoinRoot (h.map (algebraMap k (AdjoinRoot p))))
    exact hred
  exact (isRadical_iff_span_singleton.mpr hrad).squarefree
    (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)

/-- Every literal irreducible upper factor occurs once. This concerns extension
of constants, not the generally ramified extension to a root of the closed point. -/
theorem multiplicity_eq_one_of_dvd_map_separable_constant (hp : p.Separable)
    (q : (AdjoinRoot p)[X]) (hq : Irreducible q)
    (hqh : q ∣ h.map (algebraMap k (AdjoinRoot p))) :
    multiplicity q (h.map (algebraMap k (AdjoinRoot p))) = 1 := by
  apply Nat.le_antisymm
  · apply multiplicity_le_of_emultiplicity_le
    exact ((squarefree_iff_emultiplicity_le_one _).mp
      (squarefree_map_of_separable_constant p h hp) q).resolve_right hq.not_isUnit
  · exact Nat.succ_le_of_lt (multiplicity_pos_of_dvd hqh
      (FiniteMultiplicity.of_not_isUnit hq.not_isUnit
        (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)))

end AdjoinRoot
