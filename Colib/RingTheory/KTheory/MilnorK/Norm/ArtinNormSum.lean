/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparisonFinite
public import Colib.RingTheory.KTheory.MilnorK.Norm.TensorResidueFactors

import Colib.RingTheory.AdjoinRoot.LocalLength
import Colib.RingTheory.AdjoinRoot.Map
import Colib.RingTheory.AdjoinRoot.TensorScalarFactors
import Colib.RingTheory.KTheory.MilnorK.Norm.SeparableScalarFactors
import StacksFrontier.RingTheory.BaseChangeTransport

/-!
# Weighted Milnor norms on a finite Artin algebra

The weighted sum uses the residue field and localization length at each
original prime of the finite algebra. A literal polynomial presentation
identifies those lengths with the multiplicities in the coefficient image.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- Compatible residue-field maps give the same chosen norm contribution. -/
theorem norm_map_eq_of_ringEquiv {k E A B : Type u} [Field k] [Field E]
    [Field A] [Field B] [Algebra k A] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B]
    (e : A ≃+* B) (j : E →+* A) (j' : E →+* B)
    (hbase : e.toRingHom.comp (algebraMap k A) = algebraMap k B)
    (hmap : e.toRingHom.comp j = j') (x : MilnorKRing E) :
    milnorKNormRing k A (milnorKRingMap j x) =
      milnorKNormRing k B (milnorKRingMap j' x) := by
  have hcomm : e.toRingHom.comp (algebraMap k A) =
      (algebraMap k B).comp (RingEquiv.refl k).toRingHom :=
    hbase.trans (RingHom.comp_id _).symm
  have h := milnorKNormRing_map_ringEquiv_of_finite (RingEquiv.refl k)
    e hcomm (milnorKRingMap j x)
  simpa only [RingEquiv.toRingHom_refl', milnorKRingMap_id_apply,
    milnorKRingMap_comp_apply, hmap] using h

/-- The residue field of an actual point of a finite field algebra is finite. -/
theorem finiteArtinResidueField {L A : Type u} [Field L] [CommRing A]
    [Algebra L A] [Module.Finite L A] (p : PrimeSpectrum A) :
    FiniteDimensional L p.asIdeal.ResidueField := by
  let : IsArtinianRing A := IsArtinianRing.of_finite L A
  let : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  exact Module.Finite.trans A p.asIdeal.ResidueField

attribute [local instance] finiteArtinResidueField

/-- The sum of actual residue norms weighted by their local Artin lengths. -/
def weightedNormSum {L E A : Type u} [Field L] [Field E] [CommRing A]
    [Algebra L A] [Module.Finite L A] (j : E →+* A) (x : MilnorKRing E) :
    MilnorKRing L :=
  ∑ᶠ p : PrimeSpectrum A, (artinLocalLength p : ℤ) •
    milnorKNormRing L p.asIdeal.ResidueField
      (milnorKRingMap ((algebraMap A p.asIdeal.ResidueField).comp j) x)

/-- The full weighted norm sum is preserved by the actual algebra equivalence. -/
theorem weightedNormSum_algEquiv {L E A B : Type u} [Field L] [Field E]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    [Module.Finite L A] [Module.Finite L B]
    (e : A ≃ₐ[L] B) (j : E →+* A) (x : MilnorKRing E) :
    weightedNormSum (L := L) j x = weightedNormSum (L := L) (e.toRingHom.comp j) x := by
  classical
  let : IsArtinianRing A := IsArtinianRing.of_finite L A
  let : IsArtinianRing B := IsArtinianRing.of_finite L B
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  let : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  simp only [weightedNormSum, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_equiv (PrimeSpectrum.comapEquiv e.toRingEquiv).symm.toEquiv _ _ ?_
  intro q
  let p := PrimeSpectrum.comap e.toRingHom q
  let f : p.asIdeal.ResidueField →ₐ[L] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal e.toAlgHom rfl
  have hf : Function.Bijective f :=
    (RingHom.surjectiveOnStalks_of_surjective e.surjective).residueFieldMap_bijective
      p.asIdeal q.asIdeal rfl
  let e' := AlgEquiv.ofBijective f hf
  have hbase : e'.toRingHom.comp (algebraMap L p.asIdeal.ResidueField) =
      algebraMap L q.asIdeal.ResidueField := RingHom.ext e'.commutes
  have hmap : e'.toRingHom.comp ((algebraMap A p.asIdeal.ResidueField).comp j) =
      (algebraMap B q.asIdeal.ResidueField).comp (e.toRingHom.comp j) := by
    apply RingHom.ext
    intro a
    exact Ideal.ResidueField.map_algebraMap _ _ _ rfl (j a)
  change (artinLocalLength q : ℤ) • _ = (artinLocalLength p : ℤ) • _
  rw [show artinLocalLength p = artinLocalLength q from
    artinLocalLength_ringEquiv e.toRingEquiv q]
  exact congrArg (fun a : MilnorKRing L => (artinLocalLength q : ℤ) • a)
    (norm_map_eq_of_ringEquiv e'.toRingEquiv _ _ hbase hmap x).symm

/-- A literal polynomial presentation computes scalar restriction by the full Artin norm sum. -/
theorem weightedNormSum_of_presentation
    {k L E : Type u} [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
    [FiniteDimensional k E] {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (ε : E ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing E) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k E x) =
      weightedNormSum (L := L)
        (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom x := by
  classical
  let φ := algebraMap k L
  let f := (poly p).map φ
  let B := AdjoinRoot f
  let I := {r : Σ e : ℕ, MonicIrreducibleOfDegree L e // poly r.2 ∣ f}
  let : Fintype I := coefficientFactorFintype φ (poly p) (ne_zero p)
  let : ∀ r : I, FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
    fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  let : Module.Finite L B := ((monic p).map φ).finite_adjoinRoot
  let : IsArtinianRing B := IsArtinianRing.of_finite L B
  let : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  let e : (L ⊗[k] E) ≃ₐ[L] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) ε).trans
      (AdjoinRoot.baseChangeAlgEquiv k L (poly p))
  let j := (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom
  let i := e.toRingHom.comp j
  have he : i = (AdjoinRoot.map φ (poly p) f dvd_rfl).comp ε.toRingHom := by
    have hmap : (AdjoinRoot.baseChangeAlgEquiv k L (poly p)).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          AdjoinRoot (poly p) →ₐ[k] L ⊗[k] AdjoinRoot (poly p)).toRingHom =
        AdjoinRoot.map φ (poly p) f dvd_rfl := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro a
        exact (AdjoinRoot.baseChangeAlgEquiv_tmul_of k L (poly p) a).trans
          (AdjoinRoot.map_of φ (poly p) f dvd_rfl a).symm
      · exact (AdjoinRoot.baseChangeAlgEquiv_tmul_root k L (poly p)).trans
          (AdjoinRoot.map_root φ (poly p) f dvd_rfl).symm
    apply RingHom.ext
    intro a
    change e (1 ⊗ₜ[k] a) = _
    simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq]
    exact RingHom.congr_fun hmap (ε a)
  refine (milnorKNormRing_map_eq_weighted_sum_scalarFactors_of_finite φ p ε x).trans ?_
  refine Eq.trans ?_ (weightedNormSum_algEquiv e j x).symm
  simp only [weightedNormSum, finsum_eq_sum_of_fintype]
  let eI : I ≃ PrimeSpectrum B :=
    ((IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := B)).trans
      (AdjoinRoot.maximalFactorIndexEquiv f ((monic p).map φ).ne_zero)).symm
  refine Fintype.sum_equiv eI _ _ ?_
  intro r
  let μ := AdjoinRoot.nativeFactorMaximal f r
  let q := μ.toPrimeSpectrum
  have hweight : artinLocalLength q = multiplicity (poly r.1.2) f := by
    change (Module.length (Localization.AtPrime (AdjoinRoot.nativeFactorMaximal f r).asIdeal)
      (Localization.AtPrime (AdjoinRoot.nativeFactorMaximal f r).asIdeal)).toNat = _
    simpa only [ENat.toNat_natCast] using congrArg ENat.toNat
      (AdjoinRoot.branch_localLength f ((monic p).map φ).ne_zero r)
  let e₀ : (B ⧸ μ.asIdeal) ≃ₐ[L] μ.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom L (B ⧸ μ.asIdeal) μ.asIdeal.ResidueField)
      μ.asIdeal.bijective_algebraMap_quotient_residueField
  let g := e₀.symm.trans (AdjoinRoot.nativeFactorQuotientAlgEquiv f r)
  have hg (z : B) : g (algebraMap B μ.asIdeal.ResidueField z) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2) z := by
    rw [IsScalarTower.algebraMap_apply B (B ⧸ μ.asIdeal) μ.asIdeal.ResidueField]
    change AdjoinRoot.nativeFactorQuotientAlgEquiv f r
      (e₀.symm (e₀ (Ideal.Quotient.mk μ.asIdeal z))) = _
    rw [e₀.symm_apply_apply, AdjoinRoot.nativeFactorQuotientAlgEquiv_mk]
  have hinput : g.toRingHom.comp ((algebraMap B μ.asIdeal.ResidueField).comp i) =
      (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2).comp ε.toRingHom := by
    apply RingHom.ext
    intro a
    change g (algebraMap B μ.asIdeal.ResidueField (i a)) =
      AdjoinRoot.map φ (poly p) (poly r.1.2) r.2 (ε a)
    rw [hg, he, RingHom.comp_apply]
    let π : B →+* AdjoinRoot (poly r.1.2) :=
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)
    obtain ⟨b, hb⟩ := AdjoinRoot.mk_surjective (ε a)
    have h₁ : AdjoinRoot.map φ (poly p) f dvd_rfl (ε a) =
        AdjoinRoot.mk f (b.map φ) :=
      (congrArg (AdjoinRoot.map φ (poly p) f dvd_rfl) hb.symm).trans
        (AdjoinRoot.map_mk φ (poly p) f dvd_rfl b)
    have h₂ : AdjoinRoot.map φ (poly p) (poly r.1.2) r.2 (ε a) =
        AdjoinRoot.mk (poly r.1.2) (b.map φ) :=
      (congrArg (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) hb.symm).trans
        (AdjoinRoot.map_mk φ (poly p) (poly r.1.2) r.2 b)
    change π (AdjoinRoot.map φ (poly p) f dvd_rfl (ε a)) =
      AdjoinRoot.map φ (poly p) (poly r.1.2) r.2 (ε a)
    calc
      _ = π (AdjoinRoot.mk f (b.map φ)) := congrArg (fun z : B => π z) h₁
      _ = AdjoinRoot.mk (poly r.1.2) (b.map φ) := rfl
      _ = _ := h₂.symm
  have hbase : g.toRingHom.comp (algebraMap L μ.asIdeal.ResidueField) =
      algebraMap L (AdjoinRoot (poly r.1.2)) := RingHom.ext g.commutes
  change (multiplicity (poly r.1.2) f : ℤ) • _ = (artinLocalLength q : ℤ) • _
  rw [hweight]
  let : FiniteDimensional L μ.asIdeal.ResidueField := finiteArtinResidueField q
  exact congrArg (fun a : MilnorKRing L => (multiplicity (poly r.1.2) f : ℤ) • a)
    (norm_map_eq_of_ringEquiv g.toRingEquiv _ _ hbase hinput x).symm

end Stacks.Chow
