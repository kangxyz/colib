/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphNormalization
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Finite pushforward from the monic cuts on a graph support

The entire polynomial cut is pulled back to the support before pushing forward.
Its finite flat rank gives the signed normalization after any finite map from
the support to the target. This is the support calculation in Voevodsky,
Cancellation theorem (2010), Lemma 4.3.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k : Type u} [Field k] {P Z : Scheme.{u}}

/-- The whole monic quotient retains its rank after base change to the support,
including all nonreduced roots. -/
theorem polynomialSupportProjection_finrank (q : P ⟶ Spec (.of k))
    (p : k[X]) (hp : p.Monic) (x : P) :
    letI : IsFinite (projection p) := projection_isFinite p hp
    letI : Flat (projection p) := projection_flat p hp
    (pullback.fst q (projection p)).finrank x = p.natDegree := by
  let : IsFinite (projection p) := projection_isFinite p hp
  let : Flat (projection p) := projection_flat p hp
  rw [Scheme.Hom.finrank_pullback_fst]
  exact projection_finrank_eq_natDegree p hp (q x)

variable [IsNoetherian P]

/-- After the actual base change, the pushforward of the whole polynomial
quotient along a finite support map gives its degree times the original cycle. -/
theorem finiteCyclePushforward_polynomialSupport (j : P ⟶ Z) [IsFinite j]
    (q : P ⟶ Spec (.of k)) (p : k[X]) (hp : p.Monic) :
    letI : IsFinite (projection p) := projection_isFinite p hp
    letI : IsNoetherian (pullback q (projection p)) :=
      isNoetherian_of_finiteType (pullback.fst q (projection p))
    finiteCyclePushforward (pullback.fst q (projection p) ≫ j)
        (AlgebraicCycle.fundamentalCycle (pullback q (projection p))) =
      (p.natDegree : ℤ) • finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  let : IsFinite (projection p) := projection_isFinite p hp
  let : Flat (projection p) := projection_flat p hp
  let : IsNoetherian (pullback q (projection p)) :=
    isNoetherian_of_finiteType (pullback.fst q (projection p))
  rw [← finiteCyclePushforward_comp_apply (pullback.fst q (projection p)) j,
    finiteCyclePushforward_fundamentalCycle_of_constant_finrank
      (pullback.fst q (projection p)) p.natDegree
      (polynomialSupportProjection_finrank q p hp), map_zsmul]

/-- The full cut by (t^n-1) on the torus over the original support, pushed
along the original finite map. -/
def powerCutSupportCycle (j : P ⟶ Z) [IsFinite j] (q : P ⟶ Spec (.of k))
    (n : ℕ) (hn : n ≠ 0) : AlgebraicCycle Z ℤ :=
  let p := powerSubOneDenominator (R := k) n hn
  letI : IsFinite (projection p.val) := projection_isFinite p.val p.property.1
  letI : IsNoetherian (pullback q (projection p.val)) :=
    isNoetherian_of_finiteType (pullback.fst q (projection p.val))
  finiteCyclePushforward (pullback.fst q (projection p.val) ≫ j)
    (AlgebraicCycle.fundamentalCycle (pullback q (projection p.val)))

theorem powerCutSupportCycle_eq_smul (j : P ⟶ Z) [IsFinite j]
    (q : P ⟶ Spec (.of k)) (n : ℕ) (hn : n ≠ 0) :
    powerCutSupportCycle j q n hn =
      (n : ℤ) • finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  let p := powerSubOneDenominator (R := k) n hn
  exact (finiteCyclePushforward_polynomialSupport j q p.val p.property.1).trans
    (by rw [powerSubOneDenominator_natDegree n hn])

/-- The signed difference of the two monic cuts gives the original whole support
cycle, with coefficient (+1). -/
theorem identityGraph_powerCutSupportCycle_sub (j : P ⟶ Z) [IsFinite j]
    (q : P ⟶ Spec (.of k)) (n : ℕ) (hn : n ≠ 0) :
    powerCutSupportCycle j q (n + 1) (Nat.succ_ne_zero _) - powerCutSupportCycle j q n hn =
      finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  rw [powerCutSupportCycle_eq_smul, powerCutSupportCycle_eq_smul, sub_eq_add_neg, ← sub_zsmul,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_zsmul]

end AlgebraicGeometry.NativeTorusPolynomial
