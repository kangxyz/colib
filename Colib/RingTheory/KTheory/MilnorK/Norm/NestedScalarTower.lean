/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding
public import Colib.RingTheory.AdjoinRoot.NestedTowerFactor
public import Colib.RingTheory.KTheory.MilnorK.Norm.NestedScalarBranchSquare
public import Colib.RingTheory.KTheory.MilnorK.Norm.SeparableScalarFactors
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Core

/-!
# Restricted simple-norm towers from complete nested scalar factors

Every matched lower/relative pair is the actual canonical tower in the matching
top quotient. Literal identity-coefficient transport identifies its relative
norm, and the p-group tower theorem evaluates each branch. Expanding the outer
and inner norms and reindexing the entire dependent factor subtype gives the
restricted tower identity. There are no branchwise norm-comparison premises.

The splitting overfield has an independent universe. Only the original and
coefficient fields share the universe required by native Milnor restriction.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- In a coefficient field with a finite Galois p-group splitting overfield,
the two actual restricted norms agree. All factors and branch norm laws are constructed. -/
theorem simpleMilnorNorm_tower_map_of_pGroup_splitting
    {k K : Type u} [Field k] [Field K] [CharZero k] [Algebra k K]
    {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    {Ω : Type v} [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (hsplit : ((poly h).map (algebraMap k Ω)).Splits)
    (x : MilnorKRing (AdjoinRoot (poly (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p)
      (poly h) f)))))) :
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p (simpleMilnorNorm (AdjoinRoot.towerFactor
      (poly p) (poly h) f).1.2 x)) =
      milnorKRingMap (algebraMap k K) (simpleMilnorNorm h (milnorKRingMap
      ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f)).toRingHom x)) := by
  let φ := algebraMap k K
  let q := AdjoinRoot.towerFactor (poly p) (poly h) f
  let θ := AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f
  let Lower := {r : Σ a : ℕ, MonicIrreducibleOfDegree K a //
    poly (Sigma.snd r) ∣ Polynomial.map φ (poly p)}
  let Top := {s : Σ a : ℕ, MonicIrreducibleOfDegree K a //
    poly (Sigma.snd s) ∣ Polynomial.map φ (poly h)}
  let Rel (r : Lower) :=
    {t : Σ a : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly (Sigma.snd (Subtype.val r)))) a //
      poly (Sigma.snd t) ∣ Polynomial.map
        (AdjoinRoot.map φ (poly p) (poly (Sigma.snd (Subtype.val r))) (Subtype.property r))
        (poly (Sigma.snd (Subtype.val q)))}
  let Pairs := Σ r : Lower, Rel r
  classical
  let hKCharZero : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap k K).injective
  let hECharZero : CharZero (AdjoinRoot (poly p)) :=
    charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot (poly p))).injective
  let hLower : Fintype Lower := coefficientFactorFintype φ (poly p) (ne_zero p)
  let hTop : Fintype Top := coefficientFactorFintype φ (poly h) (ne_zero h)
  let hRel : ∀ r : Lower, Fintype (Rel r) := fun r =>
    coefficientFactorFintype (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2)
      (poly q.1.2) (ne_zero q.1.2)
  let branch
      (a : Σ r : {r : Σ n : ℕ, MonicIrreducibleOfDegree K n //
        poly (Sigma.snd r) ∣ Polynomial.map φ (poly p)},
        {t : Σ n : ℕ, MonicIrreducibleOfDegree
          (AdjoinRoot (poly (Sigma.snd (Subtype.val r)))) n //
          poly (Sigma.snd t) ∣ Polynomial.map
            (AdjoinRoot.map φ (poly p) (poly (Sigma.snd (Subtype.val r)))
              (Subtype.property r))
            (poly (Sigma.snd (Subtype.val
              (AdjoinRoot.towerFactor (poly p) (poly h) f))))}) : MilnorKRing K :=
    simpleMilnorNorm a.1.1.2
      (simpleMilnorNorm a.2.1.2
        (milnorKRingMap
          (AdjoinRoot.map (AdjoinRoot.map φ (poly p) (poly a.1.1.2) a.1.2)
            (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (poly a.2.1.2) a.2.2) x))
  let j (s : Top) : AdjoinRoot (poly s.1.2) →ₐ[K] Ω :=
    Classical.choice (AdjoinRoot.nonempty_algHom_branch_of_splits
      (poly h) (ne_zero h) hsplit (poly s.1.2) (irreducible s.1.2) s.2).1
  have hbranch := fun s : Top =>
    simpleMilnorNorm_nestedScalarFactor_pGroup_square φ p h f s ℓ hG (j s) x
  have houter := simpleMilnorNorm_map_eq_sum_scalarFactors φ p (simpleMilnorNorm q.1.2 x)
  have htop := simpleMilnorNorm_map_eq_sum_scalarFactors
    φ h (milnorKRingMap (θ).toRingHom x)
  have hinner :
      (∑ r : Lower, simpleMilnorNorm r.1.2
        (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2)
          (simpleMilnorNorm q.1.2 x))) =
        ∑ r : Lower, ∑ t : Rel r, branch ⟨r, t⟩ := by
    apply Finset.sum_congr rfl
    intro r _
    have hs := simpleMilnorNorm_map_eq_sum_scalarFactors
      (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) q.1.2 x
    have hnorm := congrArg (simpleMilnorNorm r.1.2) hs
    have hmap := map_sum (simpleMilnorNorm r.1.2)
      (fun t : Rel r => simpleMilnorNorm t.1.2
        (milnorKRingMap
          (AdjoinRoot.map (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2)
            (poly q.1.2) (poly t.1.2) t.2) x)) Finset.univ
    have hresult := hnorm.trans hmap
    exact hresult
  have hsigma := (Fintype.sum_sigma branch).symm
  have hpointwise := funext hbranch
  have hsum := congrArg (fun f : Top → MilnorKRing K => ∑ s, f s) hpointwise
  have hcomp := (AdjoinRoot.nestedScalarFactorIndexEquiv
    φ (poly p) (poly h) f).sum_comp branch
  dsimp only [branch] at hcomp
  dsimp only [Top] at hsum
  open Lean Elab Tactic in
  run_tac do
    withMainContext do
      let mut comp? : Option Expr := none
      let mut sum? : Option Expr := none
      for decl in ← getLCtx do
        if decl.userName.eraseMacroScopes == `hcomp then
          comp? := some (mkFVar decl.fvarId)
        if decl.userName.eraseMacroScopes == `hsum then
          sum? := some (mkFVar decl.fvarId)
      let some comp := comp? | throwError "hcomp proof not found"
      let some sum := sum? | throwError "hsum proof not found"
      let reverse ← Lean.Meta.mkEqSymm comp
      let proof ← Lean.Meta.mkEqTrans reverse sum
      let proof ← instantiateMVars proof
      let (_, goal) ← (← getMainGoal).note `hreindex proof
      replaceMainGoal [goal]
  have hresult := houter.trans (hinner.trans (hsigma.trans (hreindex.trans htop.symm)))
  exact hresult

end Stacks.Chow
end
