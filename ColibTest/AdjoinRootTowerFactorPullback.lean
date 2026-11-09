module

import Colib.RingTheory.AdjoinRoot.TowerFactorPullback

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.towerPullback_nativeIrreducible



/-- The original intermediate-field action is retained on a literal polynomial quotient. -/
example
    {k A L : Type u} [Field k] [Field A] [Field L]
    [Algebra k A] [Algebra A L] [Algebra k L] [IsScalarTower k A L]
    {d e : ℕ} (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (ε : A ≃ₐ[k] AdjoinRoot (poly p)) (η : L ≃ₐ[k] AdjoinRoot (poly h)) :
    let i := η.toAlgHom.comp ((IsScalarTower.toAlgHom k A L).comp ε.symm.toAlgHom)
    let q := AdjoinRoot.towerFactor (poly p) (poly h) i
    ∃ (r : MonicIrreducibleOfDegree A q.1.1)
      (g : L ≃ₐ[A] (A[X] ⧸ Ideal.span {poly r}))
      (hr : poly q.1.2 = (poly r).map ε.toRingHom),
      poly r = (poly q.1.2).map ε.symm.toRingHom ∧
        (AdjoinRoot.map ε.toRingHom (poly r) (poly q.1.2) (hr ▸ dvd_rfl)).comp
            g.toRingHom =
          (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p)))
            (poly h) (poly q.1.2) q.2).comp η.toRingHom :=
  AdjoinRoot.exists_towerFactor_pullback_presentation p h ε η

end
