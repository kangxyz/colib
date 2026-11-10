/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor

/-!
# Pulling the canonical tower factor back to the actual intermediate field

An actual presentation of the lower field pulls the canonical relative factor
back by its inverse coefficient map. The resulting native quotient presents the
original upper field over its original intermediate-field action. The square
with the canonical factor map is proved, not assumed. No norm occurs here.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

namespace AdjoinRoot

attribute [local instance] Ideal.Quotient.field

local instance towerPullback_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩



/-- Pull back the actual canonical factor, retaining the original `A`-action on
`L` and the exact quotient-map square. The polynomial is literally mapped by
`ε.symm`; its irreducibility and degree follow from that coefficient equivalence. -/
theorem exists_towerFactor_pullback_presentation
    {k A L : Type u} [Field k] [Field A] [Field L]
    [Algebra k A] [Algebra A L] [Algebra k L] [IsScalarTower k A L]
    {d e : ℕ} (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (ε : A ≃ₐ[k] AdjoinRoot (poly p)) (η : L ≃ₐ[k] AdjoinRoot (poly h)) :
    let i := η.toAlgHom.comp ((IsScalarTower.toAlgHom k A L).comp ε.symm.toAlgHom)
    let q := towerFactor (poly p) (poly h) i
    ∃ (r : MonicIrreducibleOfDegree A q.1.1)
      (g : L ≃ₐ[A] AdjoinRoot (poly r))
      (hr : poly q.1.2 = (poly r).map ε.toRingHom),
      poly r = (poly q.1.2).map ε.symm.toRingHom ∧
        (AdjoinRoot.map ε.toRingHom (poly r) (poly q.1.2) (hr ▸ dvd_rfl)).comp
            g.toRingHom =
          (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p)))
            (poly h) (poly q.1.2) q.2).comp η.toRingHom := by
  classical
  let i := η.toAlgHom.comp ((IsScalarTower.toAlgHom k A L).comp ε.symm.toAlgHom)
  let q := towerFactor (poly p) (poly h) i
  let r : MonicIrreducibleOfDegree A q.1.1 :=
    ⟨(poly q.1.2).map ε.symm.toRingHom, (monic q.1.2).map _, by
      change Irreducible (Polynomial.mapEquiv ε.symm.toRingEquiv (poly q.1.2))
      rw [MulEquiv.irreducible_iff]
      exact irreducible q.1.2, by
      rw [Polynomial.natDegree_map, natDegree_eq]⟩
  have hr : poly q.1.2 = (poly r).map ε.toRingHom := by
    change poly q.1.2 = ((poly q.1.2).map ε.symm.toRingHom).map ε.toRingHom
    rw [Polynomial.map_map]
    have hc : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id _ := by
      apply RingHom.ext
      intro a
      exact ε.apply_symm_apply a
    rw [hc, Polynomial.map_id]
  let c : AdjoinRoot (poly r) ≃+* AdjoinRoot (poly q.1.2) :=
    AdjoinRoot.mapRingEquiv ε.toRingEquiv (poly r) (poly q.1.2)
      (by
        change Associated ((poly r).map ε.toRingHom) (poly q.1.2)
        rw [← hr])
  let θ := towerFactorRingEquiv (poly p) (poly h) i
  have hc : c.toRingHom =
      AdjoinRoot.map ε.toRingHom (poly r) (poly q.1.2) (hr ▸ dvd_rfl) := rfl
  let v : AdjoinRoot (poly r) ≃+* L := (c.trans θ).trans η.symm.toRingEquiv
  have hv : ∀ a : A, v (algebraMap A (AdjoinRoot (poly r)) a) = algebraMap A L a := by
    intro a
    apply η.injective
    change η (η.symm (θ (c (algebraMap A (AdjoinRoot (poly r)) a)))) =
      η (algebraMap A L a)
    rw [η.apply_symm_apply]
    have hca : c (algebraMap A (AdjoinRoot (poly r)) a) =
        algebraMap (AdjoinRoot (poly p)) (AdjoinRoot (poly q.1.2)) (ε a) := by
      change c.toRingHom (AdjoinRoot.of (poly r) a) = _
      simpa only [hc, AdjoinRoot.algebraMap_eq, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv] using
        AdjoinRoot.map_of ε.toRingHom (poly r) (poly q.1.2) (hr ▸ dvd_rfl) a
    rw [hca]
    change towerFactorRingEquiv (poly p) (poly h) i
        (algebraMap (AdjoinRoot (poly p)) (AdjoinRoot (poly q.1.2)) (ε a)) = _
    rw [towerFactorRingEquiv_algebraMap]
    change η (algebraMap A L (ε.symm (ε a))) = η (algebraMap A L a)
    rw [ε.symm_apply_apply]
  let vA : AdjoinRoot (poly r) ≃ₐ[A] L := { v with commutes' := hv }
  refine ⟨r, vA.symm, hr, rfl, ?_⟩
  rw [← hc, ← towerFactorRingEquiv_symm_toRingHom]
  apply RingHom.ext
  intro z
  apply θ.injective
  change θ (c (vA.symm z)) = θ (θ.symm (η z))
  rw [θ.apply_symm_apply]
  have hvz := congrArg η (vA.apply_symm_apply z)
  change η (η.symm (θ (c (vA.symm z)))) = η z at hvz
  simpa only [η.apply_symm_apply] using hvz

end AdjoinRoot

end
