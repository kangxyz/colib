/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactorPullback
public import Colib.FieldTheory.AdjoinRoot.SeparablePresentation
public import Colib.RingTheory.KTheory.MilnorK.Norm.TowerSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport

/-!
# Reading the native simple tower through actual field presentations

The canonical relative factor is pulled back to the original intermediate
field. Exact coefficient-map naturality and the unrestricted simple tower give
the equation in those original fields. Neither chosen-norm invariance nor
polynomial presentation independence is an input.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- There is an actual polynomial presentation of `L / A` in which the two
original simple norms compose. The presentation and its map are constructed
from the canonical factor, not supplied as a norm-compatibility hypothesis. -/
theorem exists_simpleMilnorNorm_tower_presentation_of_isSeparable
    {k A L : Type u} [Field k] [Field A] [Field L]
    [Algebra k A] [Algebra A L] [Algebra k L] [IsScalarTower k A L]
    [Algebra.IsSeparable k L]
    {d e : ℕ} (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (ε : A ≃ₐ[k] AdjoinRoot (poly p)) (η : L ≃ₐ[k] AdjoinRoot (poly h)) :
    ∃ (rDegree : ℕ) (r : MonicIrreducibleOfDegree A rDegree)
      (g : L ≃ₐ[A] AdjoinRoot (poly r)),
      ∀ x : MilnorKRing L,
        simpleMilnorNorm p
            (milnorKRingMap ε.toRingHom (simpleMilnorNorm r (milnorKRingMap g.toRingHom x))) =
          simpleMilnorNorm h (milnorKRingMap η.toRingHom x) := by
  classical
  let i := η.toAlgHom.comp ((IsScalarTower.toAlgHom k A L).comp ε.symm.toAlgHom)
  let q := AdjoinRoot.towerFactor (poly p) (poly h) i
  obtain ⟨r, g, hr, _hpoly, hmap⟩ :=
    AdjoinRoot.exists_towerFactor_pullback_presentation p h ε η
  refine ⟨q.1.1, r, g, ?_⟩
  intro x
  have hnorm := simpleMilnorNorm_map_of_poly_eq_map
    ε.toRingHom r q.1.2 hr (milnorKRingMap g.toRingHom x)
  have houter := congrArg (simpleMilnorNorm p) hnorm
  have hleft := milnorKRingMap_comp_apply g.toRingHom
    (AdjoinRoot.map ε.toRingHom (poly r) (poly q.1.2) (hr ▸ dvd_rfl)) x
  have hsquare := congrArg
    (fun ψ : L →+* AdjoinRoot (poly q.1.2) => milnorKRingMap ψ x) hmap
  have hright := milnorKRingMap_comp_apply η.toRingHom
    (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p)))
      (poly h) (poly q.1.2) q.2) x
  have hmaps := hleft.trans (hsquare.trans hright.symm)
  have hrelative := congrArg (simpleMilnorNorm q.1.2) hmaps
  have hmiddle := congrArg (simpleMilnorNorm p) hrelative
  have hhsep := AdjoinRoot.polynomial_separable_of_algHom
    (poly h) (monic h) η.symm.toAlgHom
  have htower := simpleMilnorNorm_eq_tower_of_separable p h hhsep i (milnorKRingMap η.toRingHom x)
  have hresult := houter.trans (hmiddle.trans htower.symm)
  exact hresult

end Stacks.Chow

end
