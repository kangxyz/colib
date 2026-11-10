/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeEquivarianceSeparable
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Consumers of simultaneous equivariance of the actual normal-prime chosen norm.
The target fields retain their supplied algebra structures, with no target
normality, separability, or prime-degree premise. The final consumers include
finite fields and the degree-`p` extension `GaloisField p p` of `ZMod p`.
-/

noncomputable section

open Module Stacks.Chow

universe u

variable {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
  [Algebra k L] [Algebra k' L']

section SeparableNormalPrime

variable [FiniteDimensional k L] [FiniteDimensional k' L']
  [hsep : Algebra.IsSeparable k L] [hnormal : Normal k L]

include hsep hnormal

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) :=
  milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ x

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) :
    (milnorKRingMap σ.toRingHom).toAddMonoidHom.comp (milnorKNormRing k L) =
      (milnorKNormRing k' L').comp (milnorKRingMap τ.toRingHom).toAddMonoidHom :=
  milnorKNormRing_comp_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) :=
  milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n x

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) :
    (milnorKTransport σ.toRingHom n).comp (milnorKNorm k L n) =
      (milnorKNorm k' L' n).comp (milnorKTransport τ.toRingHom n) :=
  milnorKNorm_comp_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTheoryMap τ.toRingHom n x) := by
  simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
    milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n x

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) :
    (milnorKTheoryMap σ.toRingHom n).toAddMonoidHom.comp (milnorKNorm k L n) =
      (milnorKNorm k' L' n).comp (milnorKTheoryMap τ.toRingHom n).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
    milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n x

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKTheory L 0) :
    milnorKTransport σ.toRingHom 0 (milnorKNorm k L 0 x) =
      milnorKNorm k' L' 0 (milnorKTransport τ.toRingHom 0 x) :=
  milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ 0 x

/- This also allows imperfect bases whose characteristic equals the extension degree. -/
example {p : ℕ} [CharP k p] (hp : Nat.Prime p) (hdegree : finrank k L = p)
    (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) := by
  have hpL : Nat.Prime (finrank k L) := hdegree.symm ▸ hp
  exact milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable hpL σ τ hστ x

end SeparableNormalPrime

section FiniteFields

variable [Finite L] [Finite L']

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) :=
  milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ x

example (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) :=
  milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n x

end FiniteFields

/- Here the original source extension has degree `p` and characteristic `p`. -/
example (p : ℕ) [Fact p.Prime]
    (σ : ZMod p ≃+* ZMod p) (τ : GaloisField p p ≃+* GaloisField p p)
    (hστ : τ.toRingHom.comp (algebraMap (ZMod p) (GaloisField p p)) =
      (algebraMap (ZMod p) (GaloisField p p)).comp σ.toRingHom)
    (x : MilnorKRing (GaloisField p p)) :
    milnorKRingMap σ.toRingHom (milnorKNormRing (ZMod p) (GaloisField p p) x) =
      milnorKNormRing (ZMod p) (GaloisField p p) (milnorKRingMap τ.toRingHom x) := by
  have hp : Nat.Prime (finrank (ZMod p) (GaloisField p p)) := by
    rw [GaloisField.finrank p (Fact.out : Nat.Prime p).ne_zero]
    exact Fact.out
  exact milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ x

example (p : ℕ) [Fact p.Prime]
    (σ : ZMod p ≃+* ZMod p) (τ : GaloisField p p ≃+* GaloisField p p)
    (hστ : τ.toRingHom.comp (algebraMap (ZMod p) (GaloisField p p)) =
      (algebraMap (ZMod p) (GaloisField p p)).comp σ.toRingHom) (n : ℕ) :
    (milnorKTransport σ.toRingHom n).comp (milnorKNorm (ZMod p) (GaloisField p p) n) =
      (milnorKNorm (ZMod p) (GaloisField p p) n).comp (milnorKTransport τ.toRingHom n) := by
  have hp : Nat.Prime (finrank (ZMod p) (GaloisField p p)) := by
    rw [GaloisField.finrank p (Fact.out : Nat.Prime p).ne_zero]
    exact Fact.out
  exact milnorKNorm_comp_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n

end
