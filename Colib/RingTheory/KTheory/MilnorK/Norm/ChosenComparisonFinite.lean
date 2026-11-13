/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivarianceFiniteAcross
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport

/-!
# Finite chosen Milnor norms in actual field presentations

The arbitrary simple-step theorem computes the chosen norm on a native root
field by adjoining its literal root. The remaining norm is degree one. The
comparison and equivariance retain inseparable as well as separable fields.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- Compatible field isomorphisms commute with the chosen norm on the whole Milnor ring. -/
theorem milnorKNormRing_map_ringEquiv_of_finite
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) := by
  simpa only [milnorKRingMapLift_eq] using
    milnorKNormRing_map_ringEquiv_across_of_finite σ τ hστ x

/-- Compatible field isomorphisms commute with the chosen norm in each degree. -/
theorem milnorKNorm_map_ringEquiv_of_finite
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) := by
  apply Subtype.ext
  exact milnorKNormRing_map_ringEquiv_of_finite σ τ hστ (x : MilnorKRing L)

/-- Transport along a finite extension's base-algebra equivalence preserves its chosen norm. -/
theorem milnorKNorm_map_algEquiv_of_finite
    {k L L' : Type u} [Field k] [Field L] [Field L'] [Algebra k L] [Algebra k L']
    [FiniteDimensional k L] [FiniteDimensional k L']
    (ε : L ≃ₐ[k] L') (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k L' n (milnorKTheoryMap ε.toRingHom n x) = milnorKNorm k L n x := by
  have hcomm : ε.toRingHom.comp (algebraMap k L) =
      (algebraMap k L').comp (RingEquiv.refl k).toRingHom := RingHom.ext ε.commutes
  have h := milnorKNorm_map_ringEquiv_of_finite (RingEquiv.refl k)
    ε.toRingEquiv hcomm n x
  simpa only [RingEquiv.toRingHom_refl', milnorKTransport_id_apply,
    milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using h.symm

/-- On the literal polynomial root field the chosen norm is its native simple norm. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_finite
    {k : Type u} [Field k] {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    [FiniteDimensional k (AdjoinRoot (poly p))]
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKNormRing k (AdjoinRoot (poly p)) x = simpleMilnorNorm p x := by
  let P := AdjoinRoot (poly p)
  let a : P := AdjoinRoot.root (poly p)
  let J := k⟮a⟯
  let ha : IsIntegral k a := Algebra.IsIntegral.isIntegral a
  let q := minpolyOfDegree k ha
  have hpq : poly p = (poly q).map (RingHom.id k) := by
    rw [Polynomial.map_id]
    change poly p = minpoly k (AdjoinRoot.root (poly p))
    rw [AdjoinRoot.minpoly_root (ne_zero p), (monic p).leadingCoeff, inv_one, Polynomial.C_1,
      mul_one]
  let g : AdjoinRoot (poly q) →+* P :=
    AdjoinRoot.map (RingHom.id k) (poly q) (poly p) (hpq ▸ dvd_rfl)
  let e : J ≃ₐ[k] AdjoinRoot (poly q) := adjoinSimpleEquivQuot k ha
  have hj : (algebraMap J P).comp e.symm.toRingHom = g := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro t
      change (algebraMap J P) (e.symm (AdjoinRoot.of (poly q) t)) =
        g (AdjoinRoot.of (poly q) t)
      rw [AdjoinRoot.map_of]
      exact congrArg (algebraMap J P) (e.symm.commutes t)
    · change (algebraMap J P) (e.symm (AdjoinRoot.root (poly q))) =
        g (AdjoinRoot.root (poly q))
      have hr : e.symm (AdjoinRoot.root (poly q)) = AdjoinSimple.gen k a :=
        adjoinRootEquivAdjoin_apply_root k ha
      rw [AdjoinRoot.map_root, hr]
      rfl
  have htop : (k⟮a⟯ : IntermediateField k P) = ⊤ := adjoin_root_eq_top (poly p)
  have hbij : Function.Bijective (algebraMap J P) := by
    refine ⟨(algebraMap J P).injective, fun z => ?_⟩
    have hz : z ∈ (k⟮a⟯ : IntermediateField k P) := htop.symm ▸
      (IntermediateField.mem_top : z ∈ (⊤ : IntermediateField k P))
    exact ⟨⟨z, hz⟩, rfl⟩
  let inv : J ≃+* P := RingEquiv.ofBijective (algebraMap J P) hbij
  let f : P →+* AdjoinRoot (poly q) := e.toRingHom.comp inv.symm.toRingHom
  have hgf : g.comp f = RingHom.id P := by
    apply RingHom.ext
    intro y
    change g (e (inv.symm y)) = y
    rw [← hj]
    change inv (e.symm (e (inv.symm y))) = y
    rw [e.symm_apply_apply, inv.apply_symm_apply]
  have hs := simpleMilnorNorm_map_of_poly_eq_map (RingHom.id k) q p hpq (milnorKRingMap f x)
  simp only [milnorKRingMap_id_apply] at hs
  change simpleMilnorNorm q (milnorKRingMap f x) =
    simpleMilnorNorm p (milnorKRingMap g (milnorKRingMap f x)) at hs
  rw [milnorKRingMap_comp_apply, hgf, milnorKRingMap_id_apply] at hs
  rw [milnorKNormRing_eq_adjoinSimple_step_of_finite k P a, milnorKNormRing_of_bijective hbij]
  change simpleMilnorNorm q (milnorKRingMap e.toRingHom (milnorKRingMap inv.symm.toRingHom x)) = _
  rw [milnorKRingMap_comp_apply]
  exact hs

/-- A finite extension presented by a root field has the corresponding simple norm. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_finite
    {k E : Type u} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (ε : E ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing E) :
    milnorKNormRing k E x = simpleMilnorNorm p (milnorKRingMap ε.toRingHom x) := by
  let : FiniteDimensional k (AdjoinRoot (poly p)) := (AdjoinRoot.powerBasis' (monic p)).finite
  have hcomm : ε.toRingHom.comp (algebraMap k E) =
      (algebraMap k (AdjoinRoot (poly p))).comp (RingEquiv.refl k).toRingHom :=
    RingHom.ext ε.commutes
  have h := milnorKNormRing_map_ringEquiv_of_finite (RingEquiv.refl k)
    ε.toRingEquiv hcomm x
  simpa only [RingEquiv.toRingHom_refl', milnorKRingMap_id_apply,
    milnorKNormRing_eq_simpleMilnorNorm_of_finite] using h

/-- A simple presentation gives the weighted scalar factor formula for the chosen norm. -/
theorem milnorKNormRing_map_eq_weighted_sum_scalarFactors_of_finite
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p))
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}] (x : MilnorKRing L) :
    let _ : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ}, FiniteDimensional K (AdjoinRoot (poly r.1.2)) :=
      fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    milnorKRingMap φ (milnorKNormRing k L x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e // poly r.2 ∣ (poly p).map φ},
        (multiplicity (poly r.1.2) ((poly p).map φ) : ℤ) •
          milnorKNormRing K (AdjoinRoot (poly r.1.2))
            (milnorKRingMap
              ((AdjoinRoot.map φ (poly p) (poly r.1.2) r.2).comp f.toRingHom) x) := by
  intro hFinite
  let I := {r : Σ e : ℕ, MonicIrreducibleOfDegree K e // poly r.2 ∣ (poly p).map φ}
  have hinj : Set.InjOn (fun r : I => poly r.1.2) (↑(Finset.univ : Finset I) : Set I) := by
    intro r _ s _ hrs
    exact Subtype.ext (sigma_poly_injective hrs)
  have hcover : ∀ (e : ℕ) (r : MonicIrreducibleOfDegree K e), poly r ∣ (poly p).map φ →
      ∃ q ∈ (Finset.univ : Finset I), poly r = poly q.1.2 := by
    intro e r hr
    exact ⟨⟨⟨e, r⟩, hr⟩, Finset.mem_univ _, rfl⟩
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_finite p f]
  refine (simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p
    (milnorKRingMap f.toRingHom x) (Finset.univ : Finset I)
    (fun r => r.1.1) (fun r => r.1.2) hinj (fun r => r.2) hcover).trans ?_
  apply Finset.sum_congr rfl
  intro r _
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_finite r.1.2]
  let Fp := k[X] ⧸ Ideal.span {poly p}
  let Fr := K[X] ⧸ Ideal.span {poly r.1.2}
  let a : L →+* Fp := f.toRingHom
  let b : Fp →+* Fr := AdjoinRoot.map φ (poly p) (poly r.1.2) r.2
  exact congrArg
    (fun z : MilnorKRing Fr =>
      (multiplicity (poly r.1.2) ((poly p).map φ) : ℤ) • simpleMilnorNorm r.1.2 z)
    (milnorKRingMap_comp_apply a b x)

/-- The weighted scalar factor formula on the original homogeneous Milnor groups. -/
theorem milnorKNorm_map_eq_weighted_sum_scalarFactors_of_finite
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p))
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}] (n : ℕ) (x : MilnorKTheory L n) :
    let _ : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ}, FiniteDimensional K (AdjoinRoot (poly r.1.2)) :=
      fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    milnorKTransport φ n (milnorKNorm k L n x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e // poly r.2 ∣ (poly p).map φ},
        (multiplicity (poly r.1.2) ((poly p).map φ) : ℤ) •
          milnorKNorm K (AdjoinRoot (poly r.1.2)) n
            (milnorKTransport
              ((AdjoinRoot.map φ (poly p) (poly r.1.2) r.2).comp f.toRingHom) n x) := by
  intro hFinite
  apply Subtype.ext
  simpa only [milnorKTransport_coe, coe_milnorKNorm, AddSubmonoidClass.coe_finsetSum,
    AddSubgroupClass.coe_zsmul] using
    milnorKNormRing_map_eq_weighted_sum_scalarFactors_of_finite φ p f (x : MilnorKRing L)

end Stacks.Chow

end
