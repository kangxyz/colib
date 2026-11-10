module

import Colib.RingTheory.KTheory.MilnorK.Norm.NestedScalarBranchSquare

noncomputable section
open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
universe u v
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The actual coefficient-factor square gives the pointwise branch norm identity. -/
example
    {k K : Type u} [Field k] [Field K] [CharZero K]
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (s : {s : Σ a : ℕ, MonicIrreducibleOfDegree K a //
      poly s.2 ∣ (poly h).map φ})
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s.1.2) →ₐ[K] Ω)
    (x : MilnorKRing (AdjoinRoot (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2))) :
    simpleMilnorNorm (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.1.2
      (simpleMilnorNorm (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.1.2
      (@milnorKRingMap
        ((AdjoinRoot (poly p))[X] ⧸
          Ideal.span {(poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2)})
        ((AdjoinRoot (poly
          (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.1.2))[X] ⧸
          Ideal.span {(poly
            (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.1.2)})
        (Ideal.Quotient.field _) (Ideal.Quotient.field _)
        (AdjoinRoot.map (AdjoinRoot.map φ (poly p) (poly
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.1.2)
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.2) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (poly
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.1.2)
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.2) x)) =
      simpleMilnorNorm s.1.2
        (@milnorKRingMap (k[X] ⧸ Ideal.span {(poly h)})
          (K[X] ⧸ Ideal.span {(poly s.1.2)})
          (Ideal.Quotient.field _) (Ideal.Quotient.field _)
          (AdjoinRoot.map φ (poly h) (poly s.1.2) s.2)
          (@milnorKRingMap
            ((AdjoinRoot (poly p))[X] ⧸
              Ideal.span {(poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2)})
            (k[X] ⧸ Ideal.span {(poly h)})
            (Ideal.Quotient.field _) (Ideal.Quotient.field _)
            ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom) x)) := by
  have hbranch := simpleMilnorNorm_nestedScalarFactor_pGroup_square φ p h f s ℓ hG j x
  -- Keep the inferred original proof; the kernel checks the full expanded equality above.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `hbranch
      | throwError "Missing the original branch-square proof"
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar decl.fvarId)

end
