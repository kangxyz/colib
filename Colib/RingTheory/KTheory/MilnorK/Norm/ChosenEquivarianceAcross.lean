/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparisonSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleEquivarianceAcross

/-!
# Simultaneous equivariance of the native norm across universes

The source pair and the target pair can lie in independent universes. A commuting
pair of field equivalences carries an actual polynomial presentation to its coefficient
image. Separable chosen comparison on each side reduces equivariance to the simple norm.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The presentation transport of `Norm.FieldPresentationEquivariance`, with
independent source and target universes. -/
private theorem exists_monicIrreducible_presentation_ringEquiv_across
    {k L : Type u} {k' L' : Type v} [Field k] [Field L] [Field k'] [Field L']
    [Algebra k L] [Algebra k' L']
    (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom)
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) :
    ∃ (q : MonicIrreducibleOfDegree k' d)
      (g : L' ≃ₐ[k'] AdjoinRoot (poly q))
      (hq : poly q = (poly p).map σ.toRingHom),
      (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)).comp
        f.toRingHom = g.toRingHom.comp τ.toRingHom := by
  let q : MonicIrreducibleOfDegree k' d :=
    ⟨(poly p).map σ.toRingHom, (monic p).map _, by
      change Irreducible (Polynomial.mapEquiv σ (poly p))
      rw [MulEquiv.irreducible_iff]
      exact irreducible p, by
      rw [Polynomial.natDegree_map, natDegree_eq]⟩
  have hq : poly q = (poly p).map σ.toRingHom := rfl
  let c : AdjoinRoot (poly p) ≃+* AdjoinRoot (poly q) :=
    AdjoinRoot.mapRingEquiv σ (poly p) (poly q)
      (by change Associated ((poly p).map σ.toRingHom) (poly q); rw [← hq])
  have hc : c.toRingHom =
      AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl) := rfl
  have hτ (a : k') : τ.symm (algebraMap k' L' a) = algebraMap k L (σ.symm a) := by
    apply τ.injective
    rw [τ.apply_symm_apply]
    have h := congrArg (fun ψ : k →+* L' => ψ (σ.symm a)) hστ
    change τ (algebraMap k L (σ.symm a)) = algebraMap k' L' (σ (σ.symm a)) at h
    simpa only [σ.apply_symm_apply] using h.symm
  let e : L' ≃+* AdjoinRoot (poly q) := (τ.symm.trans f.toRingEquiv).trans c
  have he (a : k') : e (algebraMap k' L' a) = algebraMap k' (AdjoinRoot (poly q)) a := by
    change c (f (τ.symm (algebraMap k' L' a))) = _
    rw [hτ, f.commutes]
    change c.toRingHom (AdjoinRoot.of (poly p) (σ.symm a)) = _
    rw [hc, AdjoinRoot.map_of]
    change AdjoinRoot.of (poly q) (σ (σ.symm a)) = AdjoinRoot.of (poly q) a
    exact congrArg (AdjoinRoot.of (poly q)) (σ.apply_symm_apply a)
  let g : L' ≃ₐ[k'] AdjoinRoot (poly q) := { e with commutes' := he }
  refine ⟨q, g, hq, ?_⟩
  rw [← hc]
  apply RingHom.ext
  intro z
  change c (f z) = c (f (τ.symm (τ z)))
  rw [τ.symm_apply_apply]

/-- The native finite separable norms commute with simultaneous base and extension
equivalences that preserve the given structure maps, across independent universes. -/
theorem milnorKNormRing_map_ringEquiv_across_of_isSeparable
    {k L : Type u} {k' L' : Type v} [Field k] [Field L] [Field k'] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [Algebra.IsSeparable k L] [Algebra.IsSeparable k' L']
    (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMapLift σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMapLift τ.toRingHom x) := by
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation k L
  obtain ⟨q, g, hq, hmap⟩ :=
    exists_monicIrreducible_presentation_ringEquiv_across σ τ hστ p f
  let c := AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)
  have hleft := congrArg (milnorKRingMapLift σ.toRingHom)
    (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p f x)
  have hsimple := simpleMilnorNorm_map_of_poly_eq_map_across σ p q hq
    (milnorKRingMap f.toRingHom x)
  have hcompLeft : milnorKRingMapLift c (milnorKRingMap f.toRingHom x) =
      milnorKRingMapLift (c.comp f.toRingHom) x := by
    simpa only [milnorKRingMapLift_eq f.toRingHom] using
      milnorKRingMapLift_comp_apply f.toRingHom c x
  have hmaps := congrArg
    (fun ψ : L →+* AdjoinRoot (poly q) => milnorKRingMapLift ψ x) hmap
  have hcompRight : milnorKRingMap g.toRingHom (milnorKRingMapLift τ.toRingHom x) =
      milnorKRingMapLift (g.toRingHom.comp τ.toRingHom) x := by
    simpa only [milnorKRingMapLift_eq g.toRingHom] using
      milnorKRingMapLift_comp_apply τ.toRingHom g.toRingHom x
  have hnorm := congrArg (simpleMilnorNorm q) (hcompLeft.trans (hmaps.trans hcompRight.symm))
  have hright := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable q g
    (milnorKRingMapLift τ.toRingHom x)
  exact hleft.trans (hsimple.trans (hnorm.trans hright.symm))

end Stacks.Chow

end
