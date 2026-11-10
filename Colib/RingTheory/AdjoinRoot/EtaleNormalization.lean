/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Artinian.Module
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.BaseChangeTransport
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit

/-!
# Actual normalization branches of a separable constant cover

A monic separable polynomial remains finite étale over every coefficient algebra.
If the coefficient ring is integrally closed in its fraction field, its literal
mapped-root algebra is already the integral closure in the full generic algebra.
Every surjective field factor has finite étale native integral closure as well.

In particular this applies over an arbitrary auxiliary DVR containing the original
constant field. Neither that auxiliary field's separability over the original
Laurent field nor invertibility of any extension degree is assumed. The proof uses
the actual `AdjoinRoot`, `integralClosure`, coefficient maps and factor maps.
It proves branch geometry only, not the all-symbol Milnor norm-residue square.

The smooth-normalization and finite-product arguments adapt the private lower
proofs in pinned Stacks `DiscreteValuationRing/Abhyankar/AdjoinRootExtensions.lean`.
They use Mathlib's native smooth integral-closure comparison and do not import
that higher application or construct a replacement branch model.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace AdjoinRoot

/-- The derivative is invertible in the native quotient of a separable polynomial. -/
theorem isUnit_mk_derivative_of_separable {R : Type*} [CommRing R]
    {p : R[X]} (hsep : p.Separable) : IsUnit (AdjoinRoot.mk p p.derivative) := by
  obtain ⟨a, b, hab⟩ := hsep
  have h := congrArg (AdjoinRoot.mk p) hab
  simp only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨AdjoinRoot.mk p b, by simpa only [mul_comm] using h⟩

/-- The actual monic separable root algebra is finite étale over its original base. -/
theorem finite_etale_of_monic_of_separable {R : Type*} [CommRing R]
    {p : R[X]} (hp : p.Monic) (hsep : p.Separable) :
    Module.Finite R (AdjoinRoot p) ∧ Algebra.Etale R (AdjoinRoot p) :=
  ⟨hp.finite_adjoinRoot, Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot hp
    (isUnit_mk_derivative_of_separable hsep)⟩

/-- A separable constant cover stays finite étale under an arbitrary coefficient
map, including maps through inseparable auxiliary fields or DVRs. -/
theorem finite_etale_map_of_monic_of_separable {k R : Type*}
    [CommRing k] [CommRing R] (f : k →+* R) {p : k[X]}
    (hp : p.Monic) (hsep : p.Separable) :
    Module.Finite R (AdjoinRoot (p.map f)) ∧ Algebra.Etale R (AdjoinRoot (p.map f)) :=
  finite_etale_of_monic_of_separable (hp.map f) hsep.map

private theorem integrallyClosedIn_tensorProduct_of_smooth
    (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [IsIntegrallyClosedIn R B] [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] B) := by
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := S)
      (IsIntegralClosure.algebraMap_injective R R B)
  · intro x hx
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := B)).surjective ⟨x, hx⟩
    have hmem : (TensorProduct.toIntegralClosure R S B z : S ⊗[R] B) ∈
        (⊥ : Subalgebra S (S ⊗[R] B)) := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul s b =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral b.2
        change s ⊗ₜ[R] (b : B) ∈ (⊥ : Subalgebra S (S ⊗[R] B))
        rw [← hr]
        refine ⟨s * algebraMap R S r, ?_⟩
        change (s * algebraMap R S r) ⊗ₜ[R] 1 = s ⊗ₜ[R] algebraMap R B r
        simpa [Algebra.smul_def, mul_comm] using
          (TensorProduct.smul_tmul r s (1 : B))
      | add z w hz hw => simpa only [map_add, AddMemClass.coe_add] using
          Subalgebra.add_mem (⊥ : Subalgebra S (S ⊗[R] B)) hz hw
    rwa [hz] at hmem

private theorem exists_integralClosure_equiv_of_smooth
    (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [IsIntegrallyClosedIn R B]
    [Algebra.Smooth R S] [Algebra.IsIntegral R S] :
    Nonempty (S ≃ₐ[R] integralClosure R (S ⊗[R] B)) := by
  let := integrallyClosedIn_tensorProduct_of_smooth R S B
  let : IsIntegralClosure S R (S ⊗[R] B) := IsIntegralClosure.of_isIntegrallyClosedIn
  exact ⟨IsIntegralClosure.equiv R S (S ⊗[R] B) _⟩

/-- The literal native normalization in the complete generic root algebra is
finite étale, without choosing or discarding generic factors. -/
theorem finite_etale_integralClosure_map_of_separable
    (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
    [IsIntegrallyClosedIn R K] {p : R[X]} (hp : p.Monic) (hsep : p.Separable) :
    Module.Finite R (integralClosure R (AdjoinRoot (p.map (algebraMap R K)))) ∧
      Algebra.Etale R (integralClosure R (AdjoinRoot (p.map (algebraMap R K)))) := by
  obtain ⟨hfinite, hetale⟩ := finite_etale_of_monic_of_separable hp hsep
  let := hfinite
  let := hetale
  obtain ⟨e⟩ := exists_integralClosure_equiv_of_smooth R (AdjoinRoot p) K
  let t := (Algebra.TensorProduct.comm R (AdjoinRoot p) K).trans
    ((AdjoinRoot.baseChangeAlgEquiv R K p).restrictScalars R)
  let e' := e.trans t.mapIntegralClosure
  exact ⟨Module.Finite.equiv e'.toLinearEquiv, Algebra.Etale.of_equiv e'⟩

private theorem exists_integralClosure_pi_equiv
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] :
    ∃ e : integralClosure R (∀ i, S i) ≃ₐ[R] ∀ i, integralClosure R (S i),
      ∀ x i, (e x i : S i) = (x : ∀ i, S i) i :=
  ⟨integralClosurePiEquiv R S, fun _ _ ↦ rfl⟩

private theorem surjective_mapIntegralClosure_of_artinian
    {R T S : Type*} [CommRing R] [CommRing T] [Field S]
    [Algebra R T] [Algebra R S] [IsArtinianRing T] [IsReduced T]
    (f : T →ₐ[R] S) (hf : Function.Surjective f) :
    Function.Surjective f.mapIntegralClosure := by
  classical
  let m : MaximalSpectrum T := ⟨RingHom.ker f,
    RingHom.ker_isMaximal_of_surjective f hf⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let d := (IsArtinianRing.equivPi T).restrictScalars R
  obtain ⟨g, hg⟩ := exists_integralClosure_pi_equiv R
    (fun q : MaximalSpectrum T ↦ T ⧸ q.asIdeal)
  let h := d.mapIntegralClosure.trans g
  intro x
  let y : ∀ q : MaximalSpectrum T, integralClosure R (T ⧸ q.asIdeal) :=
    Pi.single m (e.mapIntegralClosure.symm x)
  refine ⟨h.symm y, ?_⟩
  apply Subtype.ext
  have heval : ((h (h.symm y)) m : T ⧸ m.asIdeal) =
      Ideal.Quotient.mk m.asIdeal (h.symm y : T) :=
    hg (d.mapIntegralClosure (h.symm y)) m
  rw [h.apply_symm_apply] at heval
  have hx : e (y m : T ⧸ m.asIdeal) = (x : S) := by
    dsimp only [y]
    rw [Pi.single_eq_same]
    exact congrArg Subtype.val (e.mapIntegralClosure.apply_symm_apply x)
  rwa [heval] at hx

private theorem formallyEtale_integralClosure_of_surjective
    {R T S : Type*} [CommRing R] [CommRing T] [Field S]
    [Algebra R T] [Algebra R S] [IsArtinianRing T] [IsReduced T]
    [Algebra.FormallyEtale R (integralClosure R T)]
    (f : T →ₐ[R] S) (hf : Function.Surjective f) :
    Algebra.FormallyEtale R (integralClosure R S) := by
  let m : MaximalSpectrum T := ⟨RingHom.ker f,
    RingHom.ker_isMaximal_of_surjective f hf⟩
  obtain ⟨e, _⟩ := exists_integralClosure_pi_equiv R
    (fun q : MaximalSpectrum T ↦ T ⧸ q.asIdeal)
  let := Algebra.FormallyEtale.of_equiv
    (((IsArtinianRing.equivPi T).restrictScalars R).mapIntegralClosure.trans e)
  let := (Algebra.FormallyEtale.pi_iff
    (fun q : MaximalSpectrum T ↦ integralClosure R (T ⧸ q.asIdeal))).mp
      (show Algebra.FormallyEtale R (∀ q : MaximalSpectrum T,
        integralClosure R (T ⧸ q.asIdeal)) from inferInstance) m
  exact Algebra.FormallyEtale.of_equiv
    (Ideal.quotientKerAlgEquivOfSurjective hf).mapIntegralClosure

/-- Every actual field factor of the generic separable root algebra has finite
étale native normalization. Surjectivity identifies an actual factor, and no
separability condition on any earlier coefficient extension occurs. -/
theorem finite_etale_integralClosure_of_surjective_map
    (R K E : Type*) [CommRing R] [IsNoetherianRing R] [Field K] [Field E]
    [Algebra R K] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [IsIntegrallyClosedIn R K] {p : R[X]} (hp : p.Monic) (hsep : p.Separable)
    (f : AdjoinRoot (p.map (algebraMap R K)) →ₐ[K] E) (hf : Function.Surjective f) :
    Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) := by
  obtain ⟨hfinite, hetale⟩ := finite_etale_integralClosure_map_of_separable R K hp hsep
  let := hfinite
  let := hetale
  obtain ⟨hfiniteK, hetaleK⟩ := finite_etale_map_of_monic_of_separable
    (algebraMap R K) hp hsep
  let := hfiniteK
  let := hetaleK
  let : IsArtinianRing (AdjoinRoot (p.map (algebraMap R K))) :=
    IsArtinianRing.of_finite K _
  let : IsReduced (AdjoinRoot (p.map (algebraMap R K))) :=
    Algebra.FormallyUnramified.isReduced_of_field K _
  let : Module.Finite R (integralClosure R E) :=
    Module.Finite.of_surjective (f.restrictScalars R).mapIntegralClosure.toLinearMap
      (surjective_mapIntegralClosure_of_artinian (f.restrictScalars R) hf)
  let := formallyEtale_integralClosure_of_surjective (f.restrictScalars R) hf
  let : Algebra.FinitePresentation R (integralClosure R E) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

/-- Every actual generic factor of a separable constant polynomial has finite
étale normalization over an arbitrary normal coefficient ring. The coefficient
field extension preceding this ring may be inseparable. -/
theorem finite_etale_integralClosure_constant_factor
    (k R K E : Type*) [CommRing k] [CommRing R] [IsNoetherianRing R]
    [Field K] [Field E] [Algebra k R] [Algebra R K] [Algebra k K]
    [IsScalarTower k R K] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [IsIntegrallyClosedIn R K] {p : k[X]} (hp : p.Monic) (hsep : p.Separable)
    (f : AdjoinRoot (p.map (algebraMap k K)) →ₐ[K] E) (hf : Function.Surjective f) :
    Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) := by
  have hmap : (p.map (algebraMap k R)).map (algebraMap R K) =
      p.map (algebraMap k K) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k R K]
  let e := AdjoinRoot.algEquivOfEq K _ _ hmap
  exact finite_etale_integralClosure_of_surjective_map R K E
    (hp.map (algebraMap k R)) hsep.map (f.comp e.toAlgHom) (hf.comp e.surjective)

end AdjoinRoot
