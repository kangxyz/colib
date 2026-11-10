/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalInertLocalSeparable

open Polynomial IsLocalRing Stacks.Chow
open scoped RatFunc
attribute [local instance] Polynomial.algebra Polynomial.irreducibleLocalMap_isPrime

noncomputable section

attribute [local instance]
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

variable {k : Type*} [Field k] (p h : k[X])
  [Fact p.Monic] [Fact (Irreducible p)] [Fact (Irreducible h)]
  [Fact (Irreducible (p.map (algebraMap k (AdjoinRoot h))))]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "R" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton h : Set k[X]))
local notation "pR" => Polynomial.map (algebraMap k R) p
local notation "S" => AdjoinRoot pR
local notation "hE" => Polynomial.map (algebraMap k E) h
local notation "U" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton hE : Set E[X]))
local notation "pH" => Polynomial.map (algebraMap k H) p

example : Irreducible hE := AdjoinRoot.irreducible_map_of_irreducible_opposite p h

example (a : E[X]) :
    AdjoinRoot.inertPolynomialLocalMap p h (algebraMap E[X] U a) =
      a.eval₂ (AdjoinRoot.map (algebraMap k R) p pR dvd_rfl)
        (AdjoinRoot.of pR (algebraMap k[X] R X)) :=
  AdjoinRoot.inertPolynomialLocalMap_algebraMap p h a

example : AdjoinRoot.inertPolynomialLocalMap p h (algebraMap E[X] U hE) =
    algebraMap R S (algebraMap k[X] R h) :=
  AdjoinRoot.inertPolynomialLocalMap_uniformizer p h

example : Irreducible (AdjoinRoot.inertPolynomialLocalMap p h (algebraMap E[X] U hE)) :=
  AdjoinRoot.irreducible_inertPolynomialLocalMap_uniformizer p h

example :
    (AdjoinRoot.rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom.comp
        (algebraMap U (RatFunc E)) =
      (AdjoinRoot.inertPolynomialFractionMap p h).comp
        (AdjoinRoot.inertPolynomialLocalMap p h) :=
  AdjoinRoot.inertPolynomialLocalMap_generic_square p h

example (a : ResidueField R) :
    AdjoinRoot.inertPolynomialResidueEquiv p h
        (algebraMap (ResidueField R) (ResidueField S) a) =
      algebraMap H (AdjoinRoot pH)
        ((quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm a) :=
  AdjoinRoot.inertPolynomialResidueEquiv_algebraMap p h a

example :
    (AdjoinRoot.inertPolynomialResidueEquiv p h).toRingHom.comp
        (ResidueField.map (AdjoinRoot.inertPolynomialLocalMap p h)) =
      (AdjoinRoot.tensorSwapEquiv p h).toRingHom.comp
        (quotientRingEquivResidueField (Ideal.span ({hE} : Set E[X]))).symm.toRingHom :=
  AdjoinRoot.inertPolynomialResidueEquiv_comp_residueField_map p h
