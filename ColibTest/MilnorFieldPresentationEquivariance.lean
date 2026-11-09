module

import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentationEquivariance

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

example
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom)
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) :
    ∃ (q : MonicIrreducibleOfDegree k' d)
      (g : L' ≃ₐ[k'] AdjoinRoot (poly q))
      (hq : poly q = (poly p).map σ.toRingHom),
      (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)).comp
        f.toRingHom = g.toRingHom.comp τ.toRingHom :=
  exists_monicIrreducible_presentation_ringEquiv σ τ hστ p f

end
