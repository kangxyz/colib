/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Polynomial presentation independence from the native chosen comparison

Apply the chosen comparison twice to the same original source field, once with
its identity presentation and once with the supplied algebra equivalence.
Independence of the original simple norms is a consequence, not an input, of
the unrestricted simple tower and the native recursive chosen comparison.

-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The original whole-ring simple norms agree under any actual base-algebra
presentation change in characteristic zero. The polynomial indices may differ. -/
theorem simpleMilnorNorm_map_algEquiv
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (ε : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) (x : MilnorKRing (AdjoinRoot (poly p))) :
    simpleMilnorNorm q (milnorKRingMap ε.toRingHom x) = simpleMilnorNorm p x := by
  let hFinite : FiniteDimensional k (AdjoinRoot (poly p)) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  exact (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv q ε x).symm.trans
    (milnorKNormRing_eq_simpleMilnorNorm p x)

/-- Presentation independence as equality of the original native additive maps. -/
theorem simpleMilnorNorm_comp_map_algEquiv
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (ε : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) :
    (simpleMilnorNorm q).comp (milnorKRingMap ε.toRingHom).toAddMonoidHom =
      simpleMilnorNorm p := by
  ext x
  exact simpleMilnorNorm_map_algEquiv p q ε x

/-- Independence includes every homogeneous degree with its existing transport. -/
theorem simpleMilnorNorm_milnorKTransport_algEquiv
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (ε : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) (n : ℕ)
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    simpleMilnorNorm q
        (milnorKTransport ε.toRingHom n x : MilnorKRing (AdjoinRoot (poly q))) =
      simpleMilnorNorm p (x : MilnorKRing (AdjoinRoot (poly p))) := by
  rw [milnorKTransport_coe]
  exact simpleMilnorNorm_map_algEquiv p q ε _

end Stacks.Chow

end
