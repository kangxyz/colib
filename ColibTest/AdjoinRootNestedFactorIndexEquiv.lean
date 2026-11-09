module

import Colib.RingTheory.AdjoinRoot.NestedFactorIndexEquiv
import Lean.Elab.Tactic.ElabTerm

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "q" => towerFactor p h f
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

/-- The actual original top root is preserved. -/
example (s : Top) :
    nestedScalarFactorQuotientEquiv φ p h f s
      (root (poly (nestedScalarFactorIndexEquiv φ p h f s).2.1.2)) = root (poly s.1.2) :=
  nestedScalarFactorQuotientEquiv_root φ p h f s

/-- Both original field maps are retained as pointwise equations. -/
example (s : Top) :
    let z := nestedScalarFactorIndexEquiv φ p h f s
    let ε := nestedScalarFactorQuotientEquiv φ p h f s
    (∀ a : E, ε (of (poly z.2.1.2)
      (AdjoinRoot.map φ p (poly z.1.1.2) z.1.2 a)) =
        AdjoinRoot.map φ h (poly s.1.2) s.2 (f a)) ∧
    (∀ b : H, ε (nestedScalarFactorMap φ p h f z.1 z.2 b) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 b) := by
  have hsquares := nestedScalarFactorQuotientEquiv_maps φ p h f s
  have hresult := And.intro
    (fun a : E => RingHom.congr_fun hsquares.2.1 a)
    (fun b : H => RingHom.congr_fun hsquares.1 b)
  open Lean Elab Tactic in
  run_tac do
    withMainContext do
      let mut proof? : Option Expr := none
      for decl in ← getLCtx do
        if decl.userName.eraseMacroScopes == `hresult then
          proof? := some (mkFVar decl.fvarId)
      match proof? with
      | none => throwError "Inferred consumer proof was not found"
      | some proof => closeMainGoal `inferredConsumerProof proof

/-- The relative coefficient-factor map itself, not a renamed abstract map, commutes. -/
example (s : Top) :
    let z := nestedScalarFactorIndexEquiv φ p h f s
    let ε := nestedScalarFactorQuotientEquiv φ p h f s
    ε.toRingHom.comp (AdjoinRoot.map (AdjoinRoot.map φ p (poly z.1.1.2) z.1.2)
        (poly q.1.2) (poly z.2.1.2) z.2.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp
        (towerFactorRingEquiv p h f).toRingHom :=
  (nestedScalarFactorQuotientEquiv_maps φ p h f s).2.2

end
