/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ArtinNormBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.ArtinNormSum
public import Colib.RingTheory.KTheory.MilnorK.Norm.TensorResidueFactors

/-!
# Tensor coordinates for finite Milnor norm base change

The Artin norm sum gives the formula over actual maximal quotient fields.
For a product of fields the local lengths are one, so the same sum can be
read directly in the given field coordinates.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.Chow

attribute [local instance] Ideal.Quotient.field

section MaximalQuotient

variable {k L E : Type u} [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
  [FiniteDimensional k E]

/-- Every actual maximal tensor quotient is a finite extension of the coefficient field. -/
local instance tensorNormQuotientFinite (p : MaximalSpectrum (L ⊗[k] E)) :
    FiniteDimensional L ((L ⊗[k] E) ⧸ p.asIdeal) :=
  Module.Finite.trans (L ⊗[k] E) _

/-- The chosen Milnor norm under arbitrary scalar extension is the sum over the
actual tensor residue fields, with their Artin local lengths as weights. -/
theorem milnorKNormRing_map_eq_weighted_sum_tensorFactors_of_finite
    [Fintype (MaximalSpectrum (L ⊗[k] E))] (x : MilnorKRing E) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k E x) =
      ∑ p : MaximalSpectrum (L ⊗[k] E), (tensorNormFactorLength p : ℤ) •
        milnorKNormRing L ((L ⊗[k] E) ⧸ p.asIdeal)
          (milnorKRingMap (tensorNormFactorMap p) x) := by
  classical
  let A := L ⊗[k] E
  let : IsArtinianRing A := IsArtinianRing.of_finite L A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  refine (milnorKNormRing_map_eq_weightedNormSum_tensorProduct_of_finite
    (k := k) (L := L) (E := E) x).trans ?_
  simp only [weightedNormSum, finsum_eq_sum_of_fintype]
  refine Fintype.sum_equiv IsArtinianRing.primeSpectrumEquivMaximalSpectrum _ _ ?_
  intro q
  let p := IsArtinianRing.primeSpectrumEquivMaximalSpectrum q
  let Q := A ⧸ p.asIdeal
  let R := p.asIdeal.ResidueField
  let e : Q ≃ₐ[L] R :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom L Q R)
      p.asIdeal.bijective_algebraMap_quotient_residueField
  let : FiniteDimensional L R := finiteArtinResidueField (L := L) q
  let j := (Algebra.TensorProduct.includeRight : E →ₐ[k] A).toRingHom
  have hbase : e.toRingHom.comp (algebraMap L Q) = algebraMap L R :=
    RingHom.ext e.commutes
  have hmap : e.toRingHom.comp (tensorNormFactorMap p) = (algebraMap A R).comp j := by
    apply RingHom.ext
    intro a
    exact (IsScalarTower.algebraMap_apply A Q R (j a)).symm
  change (artinLocalLength q : ℤ) • _ = (tensorNormFactorLength p : ℤ) • _
  exact congrArg (fun a : MilnorKRing L => (artinLocalLength q : ℤ) • a)
    (norm_map_eq_of_ringEquiv e.toRingEquiv _ _ hbase hmap x).symm

/-- The weighted tensor formula in each native homogeneous Milnor group. -/
theorem milnorKNorm_map_eq_weighted_sum_tensorFactors_of_finite
    [Fintype (MaximalSpectrum (L ⊗[k] E))] (n : ℕ) (x : MilnorKTheory E n) :
    milnorKTheoryMap (algebraMap k L) n (milnorKNorm k E n x) =
      ∑ p : MaximalSpectrum (L ⊗[k] E), (tensorNormFactorLength p : ℤ) •
        milnorKNorm L ((L ⊗[k] E) ⧸ p.asIdeal) n
          (milnorKTheoryMap (tensorNormFactorMap p) n x) := by
  apply Subtype.ext
  simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
    milnorKTransport_coe, coe_milnorKNorm, AddSubmonoidClass.coe_finsetSum,
    AddSubgroupClass.coe_zsmul] using
    milnorKNormRing_map_eq_weighted_sum_tensorFactors_of_finite (x : MilnorKRing E)

end MaximalQuotient

section ReducedTensor

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [FiniteDimensional F E]
  {ι : Type u} [Fintype ι] {D : ι → Type u}
  [∀ j, Field (D j)] [∀ j, Algebra K (D j)] [∀ j, FiniteDimensional K (D j)]

/-- Each field coordinate of a reduced tensor algebra contributes one norm. -/
theorem milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_finite
    (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (x : MilnorKRing E) :
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) := by
  classical
  let A := ∀ j, D j
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  let j := (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom
  let s := ε.toRingHom.comp j
  have h := (milnorKNormRing_map_eq_weightedNormSum_tensorProduct_of_finite
    (k := F) (L := K) (E := E) x).trans (weightedNormSum_algEquiv ε j x)
  refine h.trans ?_
  simp only [weightedNormSum, finsum_eq_sum_of_fintype]
  let project (i : ι) : PrimeSpectrum A := PrimeSpectrum.comap (Pi.evalRingHom D i) ⊥
  let e₀ : ι ≃ PrimeSpectrum A :=
    (Equiv.sigmaUnique ι (fun i => PrimeSpectrum (D i))).symm.trans
      (Equiv.ofBijective (PrimeSpectrum.sigmaToPi D) (PrimeSpectrum.sigmaToPi_bijective D))
  have he₀ (i : ι) : e₀ i = project i := by
    change PrimeSpectrum.sigmaToPi D
      ((Equiv.sigmaUnique ι (fun j => PrimeSpectrum (D j))).symm i) = project i
    calc
      _ = PrimeSpectrum.sigmaToPi D ⟨i, default⟩ := by rw [Equiv.sigmaUnique_symm_apply]
      _ = PrimeSpectrum.comap (Pi.evalRingHom D i) default :=
        PrimeSpectrum.sigmaToPi_apply D i _
      _ = project i := congrArg (PrimeSpectrum.comap (Pi.evalRingHom D i)) (Subsingleton.elim _ _)
  have hproject : (⇑e₀ : ι → PrimeSpectrum A) = project := funext he₀
  let e : ι ≃ PrimeSpectrum A := Equiv.ofBijective project (hproject ▸ e₀.bijective)
  symm
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  let z : PrimeSpectrum (D i) := ⊥
  let g : A →ₐ[K] D i := Pi.evalAlgHom K D i
  let q := PrimeSpectrum.comap g.toRingHom z
  let : FiniteDimensional K q.asIdeal.ResidueField := finiteArtinResidueField q
  have hg : Function.Surjective g := fun a =>
    ⟨Function.update 0 i a, Function.update_self i a 0⟩
  let g₀ : q.asIdeal.ResidueField →ₐ[K] z.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ q.asIdeal z.asIdeal g rfl
  let eg := AlgEquiv.ofBijective g₀
    ((RingHom.surjectiveOnStalks_of_surjective hg).residueFieldMap_bijective _ _ rfl)
  let f : q.asIdeal.ResidueField ≃ₐ[K] D i :=
    eg.trans ((Ideal.algEquivResidueFieldOfField z.asIdeal).restrictScalars K).symm
  have hbase : f.toRingHom.comp (algebraMap K q.asIdeal.ResidueField) =
      algebraMap K (D i) := RingHom.ext f.commutes
  have hmap : f.toRingHom.comp ((algebraMap A q.asIdeal.ResidueField).comp s) =
      g.toRingHom.comp s := by
    apply RingHom.ext
    intro a
    have he : eg (algebraMap A q.asIdeal.ResidueField (s a)) =
        algebraMap (D i) z.asIdeal.ResidueField (g (s a)) :=
      Ideal.ResidueField.map_algebraMap _ _ _ rfl (s a)
    change (Ideal.algEquivResidueFieldOfField z.asIdeal).symm
      (eg (algebraMap A q.asIdeal.ResidueField (s a))) = g (s a)
    rw [he]
    exact (Ideal.algEquivResidueFieldOfField z.asIdeal).symm_apply_apply _
  change milnorKNormRing K (D i) (milnorKRingMap (g.toRingHom.comp s) x) =
    (artinLocalLength q : ℤ) • milnorKNormRing K q.asIdeal.ResidueField
      (milnorKRingMap ((algebraMap A q.asIdeal.ResidueField).comp s) x)
  rw [artinLocalLength_eq_one q, Nat.cast_one, one_zsmul]
  exact (norm_map_eq_of_ringEquiv f.toRingEquiv _ _ hbase hmap x).symm

/-- For an actual product of fields all tensor weights are one. This comparison
retains the given coordinates and applies to arbitrary finite source fields. -/
theorem milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_finite
    (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) (x : MilnorKTheory E n) :
    milnorKTransport (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) := by
  apply Subtype.ext
  simpa only [milnorKTransport_coe, coe_milnorKNorm, AddSubmonoidClass.coe_finsetSum] using
    milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_finite ε (x : MilnorKRing E)

end ReducedTensor

end Stacks.Chow

end
