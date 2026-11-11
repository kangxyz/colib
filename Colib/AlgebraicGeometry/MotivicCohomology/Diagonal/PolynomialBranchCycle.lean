/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialSpan
public import Colib.RingTheory.AdjoinRoot.LocalLength

import Colib.RingTheory.AdjoinRoot.Map
import Mathlib.RingTheory.Artinian.Module

/-!
# Scalar polynomial quotients and their branch cycles

The tensor comparison identifies the literal scalar polynomial quotient with the
Cartesian pullback of spectra. At a branch the localization of the whole quotient
has length equal to the multiplicity of its irreducible factor. Thus the native
fundamental cycle is the weighted sum of the literal factor field cycles.
The index is the monic irreducible factor subtype used by Milnor norm base change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialBranchCycle

open AdjoinRoot Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open AlgebraicGeometry.AlgebraicCycle

variable {k L : Type u} [Field k] [Field L]

/-- The actual scalar pullback is the whole coefficient-image quotient. -/
def scalarSchemeIso (φ : k →+* L) (p : k[X]) :
    Spec (.of (AdjoinRoot (p.map φ))) ≅
      pullback (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (of p))) := by
  letI := φ.toAlgebra
  exact Scheme.Spec.mapIso
      (scalarExtensionEquiv (S := L) p).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso k L (AdjoinRoot p)).symm

/-- The projection to the new field is the original quotient scalar structure. -/
@[reassoc]
theorem scalarSchemeIso_hom_fst (φ : k →+* L) (p : k[X]) :
    (scalarSchemeIso φ p).hom ≫ pullback.fst _ _ =
      NativeTorusPolynomial.projection (p.map φ) := by
  let := φ.toAlgebra
  change (((Scheme.Spec.mapIso
      (scalarExtensionEquiv (S := L) p).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso k L (AdjoinRoot p)).inv) ≫ pullback.fst _ _) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (scalarExtensionEquiv (S := L) p).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (scalarExtensionEquiv (S := L) p).commutes

/-- The projection to the old quotient is the native coefficient map. -/
@[reassoc]
theorem scalarSchemeIso_hom_snd (φ : k →+* L) (p : k[X]) :
    (scalarSchemeIso φ p).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl)) := by
  let := φ.toAlgebra
  change (((Scheme.Spec.mapIso
      (scalarExtensionEquiv (S := L) p).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso k L (AdjoinRoot p)).inv) ≫ pullback.snd _ _) = _
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (scalarExtensionEquiv (S := L) p).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact scalarExtensionEquiv_comp_includeRight p

/-- The literal closed immersion of a native irreducible factor. -/
def branchMap (f : k[X])
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}) :
    Spec (.of (AdjoinRoot (poly r.1.2))) ⟶ Spec (.of (AdjoinRoot f)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)))

instance (f : k[X])
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}) :
    IsClosedImmersion (branchMap f r) :=
  IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr r.2))

/-- The branch over the scalar quotient carries the original old-root map. -/
@[reassoc]
theorem branchMap_scalarMap (φ : k →+* L) (p : k[X])
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e // poly r.2 ∣ p.map φ}) :
    branchMap (p.map φ) r ≫
      Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl)) =
        Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (poly r.1.2) r.2)) := by
  unfold branchMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective x
  change Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)
    (AdjoinRoot.map φ p (p.map φ) dvd_rfl (mk p a)) =
    AdjoinRoot.map φ p (poly r.1.2) r.2 (mk p a)
  rw [map_mk, map_mk]
  rfl

/-- Each branch projects to the new field through its own quotient scalar map. -/
@[reassoc]
theorem branchMap_projection (f : k[X])
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}) :
    branchMap f r ≫ NativeTorusPolynomial.projection f =
      NativeTorusPolynomial.projection (poly r.1.2) := by
  unfold branchMap NativeTorusPolynomial.projection
  rw [← Spec.map_comp]
  rfl

private theorem branchMap_genericPoint (f : k[X])
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f})
    [Fact (Irreducible (poly r.1.2))] :
    branchMap f r (genericPoint (Spec (.of (AdjoinRoot (poly r.1.2))))) =
      (nativeFactorMaximal f r).toPrimeSpectrum := by
  apply PrimeSpectrum.ext
  change Ideal.comap _ (genericPoint (Spec (.of (AdjoinRoot (poly r.1.2))))).asIdeal = _
  rw [genericPoint_eq_bot_of_affine, PrimeSpectrum.asIdeal_bot]
  rfl

/-- The actual Artin stalk over an irreducible factor has the full factor multiplicity. -/
theorem branch_stalkLength (f : k[X]) (hf : f ≠ 0)
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}) :
    let z : Spec (.of (AdjoinRoot f)) := (nativeFactorMaximal f r).toPrimeSpectrum
    Module.length ((Spec (.of (AdjoinRoot f))).presheaf.stalk z)
      ((Spec (.of (AdjoinRoot f))).presheaf.stalk z) = multiplicity (poly r.1.2) f := by
  let z : Spec (.of (AdjoinRoot f)) := (nativeFactorMaximal f r).toPrimeSpectrum
  let A := Localization.AtPrime z.asIdeal
  let R := (Spec (.of (AdjoinRoot f))).presheaf.stalk z
  let e : R ≃+* A :=
    (AlgebraicGeometry.Spec.stalkIso (.of (AdjoinRoot f)) z).commRingCatIsoToRingEquiv
  let : RingHomInvPair (e : R →+* A) (e.symm : A →+* R) := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair (e.symm : A →+* R) (e : R →+* A) :=
    RingHomInvPair.symm (e : R →+* A) (e.symm : A →+* R)
  have h : Module.length R R = Module.length A A := by
    apply WithBot.coe_injective
    rw [Module.coe_length, Module.coe_length,
      Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e.toSemilinearEquiv)]
  exact h.trans (AdjoinRoot.branch_localLength f hf r)

/-- The full quotient cycle has the native multiplicity on each original branch. -/
theorem fundamentalCycle_eq_weighted_sum_branches (f : k[X]) (hf : f.Monic)
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}] :
    fundamentalCycle (Spec (.of (AdjoinRoot f))) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f},
        (multiplicity (poly r.1.2) f : ℤ) • finiteCyclePushforward (branchMap f r)
          (fundamentalCycle (Spec (.of (AdjoinRoot (poly r.1.2))))) := by
  classical
  let : Module.Finite k (AdjoinRoot f) := hf.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot f) := .of_finite k _
  let := NativeTorusPolynomial.projection_isFinite f hf
  have hgeneric (a : Spec (.of (AdjoinRoot f))) : a ∈ genericPoints (Spec (.of (AdjoinRoot f))) :=
    mem_genericPoints_of_isFinite_image (NativeTorusPolynomial.projection f) a (by
      rw [Subsingleton.elim (NativeTorusPolynomial.projection f a) (genericPoint (Spec (.of k)))]
      exact genericPoint_mem_genericPoints _)
  let e : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f} ≃
      genericPoints (Spec (.of (AdjoinRoot f))) :=
    (maximalFactorIndexEquiv f hf.ne_zero).symm.trans
      (IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.trans
        (Equiv.subtypeUnivEquiv hgeneric).symm)
  let := (fundamentalCycle_genericPoints_finite (Spec (.of (AdjoinRoot f)))).fintype
  rw [fundamentalCycle, ofGenericCoefficients_eq_sum]
  symm
  apply Fintype.sum_equiv e
  intro r
  let : Fact (Irreducible (poly r.1.2)) := ⟨irreducible r.1.2⟩
  rw [finiteCyclePushforward_fundamentalCycle_integral, branchMap_genericPoint]
  let z : Spec (.of (AdjoinRoot f)) := (nativeFactorMaximal f r).toPrimeSpectrum
  change (multiplicity (poly r.1.2) f : ℤ) • single z (1 : ℤ) =
    single z ((Module.length ((Spec (.of (AdjoinRoot f))).presheaf.stalk z)
      ((Spec (.of (AdjoinRoot f))).presheaf.stalk z)).toNat : ℤ)
  rw [branch_stalkLength f hf.ne_zero r, ENat.toNat_natCast]
  apply Function.locallyFinsuppWithin.ext
  intro x
  simp only [coe_zsmul, Pi.smul_apply, single_apply]
  split_ifs <;> simp

/-- An irreducible branch of a squarefree polynomial has multiplicity one. -/
theorem branch_multiplicity_eq_one_of_squarefree (f : k[X]) (hf : f ≠ 0) (hs : Squarefree f)
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}) :
    multiplicity (poly r.1.2) f = 1 := by
  have hq := (irreducible r.1.2).not_isUnit
  apply Nat.le_antisymm
  · apply multiplicity_le_of_emultiplicity_le
    exact ((squarefree_iff_emultiplicity_le_one f).mp hs (poly r.1.2)).resolve_right hq
  · exact Nat.succ_le_of_lt (multiplicity_pos_of_dvd r.2 (FiniteMultiplicity.of_not_isUnit hq hf))

/-- Each distinct irreducible factor contributes one native prime cycle in the squarefree case. -/
theorem fundamentalCycle_eq_sum_branches (f : k[X]) (hf : f.Monic) (hs : Squarefree f)
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}] :
    fundamentalCycle (Spec (.of (AdjoinRoot f))) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f},
        finiteCyclePushforward (branchMap f r)
          (fundamentalCycle (Spec (.of (AdjoinRoot (poly r.1.2))))) := by
  simpa only [branch_multiplicity_eq_one_of_squarefree f hf.ne_zero hs, Nat.cast_one, one_zsmul]
    using fundamentalCycle_eq_weighted_sum_branches f hf

end AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialBranchCycle
