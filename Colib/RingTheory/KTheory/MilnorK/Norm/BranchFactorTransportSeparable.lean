/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PGroupTowerSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport

/-!
# A native p-group tower through an actual relative quotient comparison

Only polynomial identity and literal quotient-map compatibility are inputs.
There is no norm comparison hypothesis and no selected scalar-factor index.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Stacks.Chow.towerTransport_nativeIrreducible

variable {K : Type u} [Field K]
  {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- Algebraic comparison with the canonical relative quotient suffices for the native norm tower. -/
theorem simpleMilnorNorm_pGroup_tower_of_quotient_comparison_of_isGalois
    {d e m : ℕ} (r : MonicIrreducibleOfDegree K d) (s : MonicIrreducibleOfDegree K e)
    (i : AdjoinRoot (poly r) →ₐ[K] AdjoinRoot (poly s))
    (t : MonicIrreducibleOfDegree (AdjoinRoot (poly r)) m)
    (c : AdjoinRoot (poly t) ≃+* AdjoinRoot (poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2))
    (ε : AdjoinRoot (poly t) ≃+* AdjoinRoot (poly s))
    (hpoly : poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2 = (poly t).map (RingHom.id
      (AdjoinRoot (poly r))))
    (hc : c.toRingHom = AdjoinRoot.map (RingHom.id (AdjoinRoot (poly r)))
      (poly t) (poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2) (hpoly ▸ dvd_rfl))
    (hcomp : (AdjoinRoot.towerFactorRingEquiv (poly r) (poly s) i).toRingHom.comp c.toRingHom =
      ε.toRingHom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s) →ₐ[K] Ω) (y : MilnorKRing (AdjoinRoot (poly t))) :
    simpleMilnorNorm r (simpleMilnorNorm t y) =
      simpleMilnorNorm s (milnorKRingMap ε.toRingHom y) := by
  let q := AdjoinRoot.towerFactor (poly r) (poly s) i
  let θ := AdjoinRoot.towerFactorRingEquiv (poly r) (poly s) i
  have htransport := simpleMilnorNorm_map_of_poly_eq_map
    (RingHom.id (AdjoinRoot (poly r))) t q.1.2 hpoly y
  have hid := milnorKRingMap_id_apply (simpleMilnorNorm t y)
  have htransportId := hid.symm.trans htransport
  have hcApply := congrArg (fun ψ : _ →+* _ => milnorKRingMap ψ y) hc
  have hcNorm := congrArg (simpleMilnorNorm q.1.2) hcApply
  have hnorm := htransportId.trans hcNorm.symm
  have houter := congrArg (simpleMilnorNorm r) hnorm
  have htower := simpleMilnorNorm_pGroup_tower_of_isGalois r s i ℓ hG j
    (milnorKRingMap c.toRingHom y)
  have hfunctor := milnorKRingMap_comp_apply c.toRingHom θ.toRingHom y
  have hcompApply := congrArg (fun ψ : _ →+* _ => milnorKRingMap ψ y) hcomp
  have hfinish := congrArg (simpleMilnorNorm s) (hfunctor.trans hcompApply)
  have hresult := houter.trans (htower.trans hfinish)
  exact hresult

end Stacks.Chow
end
