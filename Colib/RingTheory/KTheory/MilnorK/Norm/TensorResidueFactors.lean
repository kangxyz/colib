/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# Residue factors and local lengths for finite tensor algebras

The branches of a finite field tensor algebra are its actual maximal ideals.
The weight at a branch is the length of the prime localization over itself.
In a flat tower the native spectrum fiber identifies the refinements of each
branch, and their weights multiply with the length of the lower branch.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.Chow

/-- The local length of a ring at an actual prime point. -/
def artinLocalLength {A : Type u} [CommRing A] (p : PrimeSpectrum A) : ℕ :=
  let R := Localization.AtPrime p.asIdeal
  (Module.length R R).toNat

private theorem self_length_eq_of_ringEquiv {A B : Type u}
    [CommRing A] [CommRing B] (e : A ≃+* B) :
    Module.length A A = Module.length B B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let f : A ≃ₐ[A] B := AlgEquiv.ofBijective (Algebra.ofId A B) e.bijective
  exact f.toLinearEquiv.length_eq.trans (Module.length_eq_of_surjective e.surjective)

/-- An isomorphism of rings preserves the weights at corresponding points. -/
theorem artinLocalLength_ringEquiv {A B : Type u}
    [CommRing A] [CommRing B] (e : A ≃+* B) (q : PrimeSpectrum B) :
    artinLocalLength (PrimeSpectrum.comap e.toRingHom q) = artinLocalLength q := by
  exact congrArg ENat.toNat
    (self_length_eq_of_ringEquiv (Localization.localRingEquiv
      (PrimeSpectrum.comap e.toRingHom q).asIdeal q.asIdeal e rfl))

/-- All localizations of a reduced Artinian ring have length one. -/
theorem artinLocalLength_eq_one {A : Type u} [CommRing A] [IsArtinianRing A] [IsReduced A]
    (p : PrimeSpectrum A) : artinLocalLength p = 1 := by
  let R := Localization.AtPrime p.asIdeal
  let : Field R := (IsArtinianRing.isField_of_isReduced_of_isLocalRing R).toField
  change (Module.length R R).toNat = 1
  simp

/-- The actual prime points in the fibers over the base are all the prime points
of the upper algebra, with their original contraction maps. -/
def artinSpectrumFiberEquiv (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (Σ p : PrimeSpectrum A, PrimeSpectrum (p.asIdeal.Fiber B)) ≃ PrimeSpectrum B :=
  (Equiv.sigmaCongrRight fun p => (PrimeSpectrum.preimageEquivFiber A B p).symm).trans
    (Equiv.sigmaFiberEquiv (PrimeSpectrum.comap (algebraMap A B)))

/-- A point of an actual fiber contracts by the original tensor map. -/
theorem artinSpectrumFiberEquiv_apply {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    artinSpectrumFiberEquiv A B ⟨p, q⟩ =
      PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B).toRingHom q := rfl

private theorem localLength_mul_of_closedFiber {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (e : T ≃+* S ⧸ extendedMaximalIdeal R S) :
    (Module.length R R).toNat * (Module.length T T).toNat =
      (Module.length S S).toNat := by
  have hquot : Module.length T T = Module.length S (S ⧸ extendedMaximalIdeal R S) :=
    (self_length_eq_of_ringEquiv e).trans
      (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm
  have h : Module.length R R * Module.length T T = Module.length S S :=
    (congrArg (fun n : ℕ∞ => Module.length R R * n) hquot).trans
      ((length_baseChange_eq_length_mul_length_quotient R S R).trans
        (TensorProduct.AlgebraTensorModule.rid R S S).length_eq)
  simpa only [ENat.toNat_mul] using congrArg ENat.toNat h

/-- The weights of two consecutive branches multiply, since their actual prime
localizations form a flat local map and the local fiber is its closed fiber. -/
theorem artinLocalLength_fiber_mul {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B]
    (p : PrimeSpectrum A) (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    artinLocalLength p * artinLocalLength q =
      artinLocalLength (artinSpectrumFiberEquiv A B ⟨p, q⟩) := by
  let Q := q.asIdeal
  let P := p.asIdeal
  have : Q.IsPrime := q.isPrime
  have : P.IsPrime := p.isPrime
  let r : Ideal B := Q.comap
    (Algebra.TensorProduct.includeRight : B →ₐ[A] P.Fiber B)
  have : r.IsPrime := Ideal.comap_isPrime _ _
  let Rp := Localization.AtPrime P
  let Sq := Localization.AtPrime r
  let Fq := Localization.AtPrime Q
  have : r.LiesOver P :=
    Ideal.LiesOver.of_eq_comap P (Q := Q)
      (Algebra.TensorProduct.includeRight : B →ₐ[A] P.Fiber B) rfl
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver P r
  have hlocal : algebraMap Rp Sq =
      Localization.localRingHom P r (algebraMap A B) (r.over_def P) := rfl
  have : IsLocalHom (algebraMap Rp Sq) := by
    rw [hlocal]
    exact Localization.isLocalHom_localRingHom P r (algebraMap A B) (r.over_def P)
  have : Module.Flat Rp Sq := by
    rw [← RingHom.flat_algebraMap_iff, hlocal]
    exact (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A B›).localRingHom r P (r.over_def P)
  let I := P.map (algebraMap A Sq)
  have hI : extendedMaximalIdeal Rp Sq = I := by
    have hmax : P.map (algebraMap A Rp) = IsLocalRing.maximalIdeal Rp :=
      Localization.AtPrime.map_eq_maximalIdeal (I := P)
    have hmap : (algebraMap Rp Sq).comp (algebraMap A Rp) = algebraMap A Sq :=
      (IsScalarTower.algebraMap_eq A Rp Sq).symm
    calc
      _ = (P.map (algebraMap A Rp)).map (algebraMap Rp Sq) :=
        congrArg (fun J : Ideal Rp => J.map (algebraMap Rp Sq)) hmax.symm
      _ = P.map ((algebraMap Rp Sq).comp (algebraMap A Rp)) := Ideal.map_map _ _
      _ = I := congrArg (fun f : A →+* Sq => P.map f) hmap
  let e₀ : Fq ≃ₐ[Rp] Sq ⧸ I := Ideal.Fiber.localizationAlgEquivQuotient P Q
  let e : Fq ≃+* Sq ⧸ extendedMaximalIdeal Rp Sq :=
    e₀.toRingEquiv.trans (Ideal.quotEquivOfEq hI.symm)
  have h : (Module.length Rp Rp).toNat * (Module.length Fq Fq).toNat =
      (Module.length Sq Sq).toNat :=
    localLength_mul_of_closedFiber (R := Rp) (S := Sq) (T := Fq) e
  rw [artinSpectrumFiberEquiv_apply]
  exact h

/-- Passing to the fiber over an Artinian point preserves the residue field of
each actual point above it. -/
def artinFiberResidueEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsArtinianRing A] [Algebra A B] (p : PrimeSpectrum A)
    (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    (artinSpectrumFiberEquiv A B ⟨p, q⟩).asIdeal.ResidueField ≃+* q.asIdeal.ResidueField := by
  let g : B →+* p.asIdeal.Fiber B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B).toRingHom
  haveI : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have hsurj : Function.Surjective g :=
    TensorProduct.mk_surjective _ _ _ p.asIdeal.algebraMap_residueField_surjective
  let r := (artinSpectrumFiberEquiv A B ⟨p, q⟩).asIdeal
  have hr : r = q.asIdeal.comap g := rfl
  exact RingEquiv.ofBijective (Ideal.ResidueField.map r q.asIdeal g hr)
    ((RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective
      r q.asIdeal hr)

/-- The residue comparison carries the original upper-algebra elements into
the fiber by the original right tensor map. -/
theorem artinFiberResidueEquiv_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    [IsArtinianRing A] [Algebra A B] (p : PrimeSpectrum A)
    (q : PrimeSpectrum (p.asIdeal.Fiber B)) (x : B) :
    artinFiberResidueEquiv p q
        (algebraMap B (artinSpectrumFiberEquiv A B ⟨p, q⟩).asIdeal.ResidueField x) =
      algebraMap (p.asIdeal.Fiber B) q.asIdeal.ResidueField
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B) x) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ x

section Tensor

variable {k L E : Type u} [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]

/-- The actual map of the extension field into a maximal tensor quotient. -/
def tensorNormFactorMap (p : MaximalSpectrum (L ⊗[k] E)) :
    E →+* (L ⊗[k] E) ⧸ p.asIdeal :=
  (Ideal.Quotient.mk p.asIdeal).comp
    (Algebra.TensorProduct.includeRight : E →ₐ[k] (L ⊗[k] E)).toRingHom

/-- The weight at a maximal ideal of the actual tensor algebra. -/
def tensorNormFactorLength (p : MaximalSpectrum (L ⊗[k] E)) : ℕ :=
  artinLocalLength p.toPrimeSpectrum

end Tensor

end Stacks.Chow

end
