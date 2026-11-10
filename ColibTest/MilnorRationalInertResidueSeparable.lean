/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalInertResidueSeparable

open Polynomial IsLocalRing Module Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Polynomial.irreducibleLocalMap_isPrime

noncomputable section

attribute [local instance] Ideal.Quotient.field
  AdjoinRoot.inertPolynomial_baseMaximal
  AdjoinRoot.inertPolynomial_oppositeIrreducible
  AdjoinRoot.inertPolynomial_upperMaximal
  AdjoinRoot.inertPolynomial_residueIrreducible
  AdjoinRoot.inertPolynomial_sourceDomain
  AdjoinRoot.inertPolynomial_sourceLocal
  AdjoinRoot.inertPolynomial_sourceLocalHom
  AdjoinRoot.inertPolynomial_baseDVR
  AdjoinRoot.inertPolynomial_upperDVR
  AdjoinRoot.inertPolynomial_sourceDVR
  AdjoinRoot.inertPolynomialLocalMap_isLocalHom
  inertConstant_finite
  inertConstant_torsionFree
  inertConstant_finiteGeneric

attribute [local instance]
  rationalInert_nativeMonic rationalInert_nativeIrreducible rationalInert_rootFinite
  rationalInert_rationalFinite rationalInert_genericIrreducible
  rationalInert_residueFinite rationalInert_genericFinite rationalInert_constantTower
  rationalInertFractionAlgebra rationalInert_fractionTower rationalInert_isFractionRing

universe u

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  [hinert : Fact (Irreducible ((poly p).map (algebraMap k (AdjoinRoot (poly h)))))]

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "R" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton (poly h) : Set k[X]))
local notation "S" => AdjoinRoot (Polynomial.map (algebraMap k R) (poly p))
local notation "G" => AdjoinRoot (Polynomial.map (RatFunc.C : k →+* RatFunc k) (poly p))
local notation "hE" => Polynomial.map (algebraMap k E) (poly h)
local notation "pH" => Polynomial.map (algebraMap k H) (poly p)
local notation "U" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton hE : Set E[X]))

example (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1)) :
    milnorKTheoryMap (AdjoinRoot.inertPolynomialResidueEquiv (poly p) (poly h)).toRingHom n
        (dvrMilnorTameSymbol' S G n
          (milnorKTheoryMap
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
            (n + 1) x)) =
      milnorKTheoryMap ((AdjoinRoot.tensorSwapEquiv (poly p) (poly h)).toRingHom.comp
        (quotientRingEquivResidueField (Ideal.span ({hE} : Set E[X]))).symm.toRingHom) n
        (dvrMilnorTameSymbol' U (RatFunc E) n x) :=
  dvrMilnorTameSymbol'_inertPolynomialLocalMap p h n x

variable [hnormal : Normal k (AdjoinRoot (poly p))]

include hnormal

set_option backward.isDefEq.respectTransparency false in
example
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (z : MilnorKTheory (ResidueField S) n) :
    milnorKTheoryMap (quotientRingEquivResidueField (Ideal.span {poly h})).symm.toRingHom n
        (milnorKNorm (ResidueField R) (ResidueField S) n z) =
      milnorKNorm H (AdjoinRoot pH) n
        (milnorKTheoryMap
          (AdjoinRoot.inertPolynomialResidueEquiv (poly p) (poly h)).toRingHom n z) :=
  milnorKNorm_inertPolynomialResidueEquiv_of_separable p h hsep hp n z

set_option backward.isDefEq.respectTransparency false in
example
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      milnorKNormRing H (AdjoinRoot pH)
        (milnorKRingMap
          ((AdjoinRoot.tensorSwapEquiv (poly p) (poly h)).toRingHom :
            (E[X] ⧸ Ideal.span {poly (inertUpperPoint p h)}) →+* AdjoinRoot pH)
          (monicIrreducibleResidue (inertUpperPoint p h) (x : MilnorKRing (RatFunc E)))) :=
  monicIrreducibleResidue_milnorKNorm_ratFunc_of_inert_of_separable p h hsep hp n x

include hinert in
set_option backward.isDefEq.respectTransparency false in
example
    (hsep : (poly p).Separable) (hp : d.Prime)
    (T : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hT : ∀ q, q ∈ T ↔ poly q.2 ∣ hE)
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      ∑ i ∈ T.attach,
        let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f // poly q.2 ∣ hE} :=
          ⟨i.1, (hT i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (@milnorKRingMap
            (E[X] ⧸ Ideal.span {poly q.1.2}) (H[X] ⧸ Ideal.span {poly r.1.2})
            (Ideal.Quotient.field _) (Ideal.Quotient.field _)
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E)))) :=
  monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_inert p h hsep hp T hT n x

