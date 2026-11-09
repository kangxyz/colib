/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.NestedFactorIndex
import Lean.Elab.Tactic.ElabTerm

/-!
# Root and map compatibility for the complete nested factor index

The literal index and chosen quotient equivalence are provided by NestedFactorIndex.
This upper layer retains their original root and map compatibility statements.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

attribute [local instance] instFactIrreduciblePolynomialPoly_colib

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "q" => towerFactor p h f
local notation "Q" => AdjoinRoot (poly (Sigma.snd (Subtype.val q)))
local notation "Lower" =>
  {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd r) ∣ Polynomial.map φ p}
local notation "Top" =>
  {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd s) ∣ Polynomial.map φ h}
local notation "Rel" r =>
  {t : Σ d : ℕ,
      MonicIrreducibleOfDegree (AdjoinRoot (poly (Sigma.snd (Subtype.val r)))) d //
    poly (Sigma.snd t) ∣ Polynomial.map
      (AdjoinRoot.map φ p (poly (Sigma.snd (Subtype.val r))) (Subtype.property r))
      (poly (Sigma.snd (Subtype.val q)))}
local notation "Pairs" => Σ r : Lower, Rel r

/-- The quotient comparison preserves the original top root. -/
theorem nestedScalarFactorQuotientEquiv_root (s : Top) :
    nestedScalarFactorQuotientEquiv φ p h f s
      (root (poly (nestedScalarFactorIndexEquiv φ p h f s).2.1.2)) = root (poly s.1.2) :=
  by
    have hroot :=
      (exists_nestedScalarFactor_pair_quotientAlgEquiv φ p h f s).choose_spec.choose_spec
    open Lean Elab Tactic in
    run_tac do
      withMainContext do
        let mut proof? : Option Expr := none
        for decl in ← getLCtx do
          if decl.userName.eraseMacroScopes == `hroot then
            proof? := some (mkFVar decl.fvarId)
        match proof? with
        | none => throwError "Local root proof was not found"
        | some proof => closeMainGoal `originalLocalRootProof proof


/-- The quotient comparison attached to the bijection preserves all original maps. -/
theorem nestedScalarFactorQuotientEquiv_maps (s : Top) :
    let z := nestedScalarFactorIndexEquiv φ p h f s
    let ε := nestedScalarFactorQuotientEquiv φ p h f s
    ε.toRingHom.comp (nestedScalarFactorMap φ p h f z.1 z.2) =
        AdjoinRoot.map φ h (poly s.1.2) s.2 ∧
    (ε.toRingHom.comp (of (poly z.2.1.2))).comp
        (AdjoinRoot.map φ p (poly z.1.1.2) z.1.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom ∧
    ε.toRingHom.comp (AdjoinRoot.map (AdjoinRoot.map φ p (poly z.1.1.2) z.1.2)
        (poly q.1.2) (poly z.2.1.2) z.2.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp
        (towerFactorRingEquiv p h f).toRingHom :=
  by
    let z := nestedScalarFactorIndexEquiv φ p h f s
    have hsquare := nestedScalarFactor_quotientEquiv_squares φ p h f z.1 z.2 s
      (nestedScalarFactorQuotientEquiv φ p h f s)
      (nestedScalarFactorQuotientEquiv_root φ p h f s)
    exact hsquare

end AdjoinRoot

end
