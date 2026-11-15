/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Components
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycleImages

/-!
# The two finite sums in exterior composition interchange

Both sides of interchange are expanded on the actual native generic labels.
Composing the product correspondences retains the generic lengths of both
product supports before the incidence Tor pairing. Taking the product of
the two composites retains the original incidence Tor coefficients and every
finite residue degree before taking the product of the image supports.

The two sums have distinct labels and coefficients. This module does not
assert their equality: that comparison needs product-diagonal Tor Euler
multiplicativity and finite exterior pushforward.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]
  (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)
  (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (hb : IsFiniteCorrespondencePoint Y.hom Z.hom b)
  (hc : IsFiniteCorrespondencePoint U.hom V.hom c)
  (hd : IsFiniteCorrespondencePoint V.hom W.hom d)

local notation "D₁" => correspondenceExteriorSupport X Y U V
  (integralComponentAt a) (integralComponentAt c)
local notation "D₂" => correspondenceExteriorSupport Y Z V W
  (integralComponentAt b) (integralComponentAt d)
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom
local notation "I" => correspondenceIncidence X.hom Y.hom Z.hom a b
local notation "J" => correspondenceIncidence U.hom V.hom W.hom c d
local notation "qI" => correspondenceIncidenceMap X.hom Y.hom Z.hom a b
local notation "qJ" => correspondenceIncidenceMap U.hom V.hom W.hom c d

/-- Composition of the product primes retains both actual product-length weights. -/
theorem incidenceTorPairing_exteriorPrimes_eq_sum :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
    letI := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
    incidenceTorPairing f g h
      (correspondenceExteriorPrime X Y U V a c ha hc)
      (correspondenceExteriorPrime Y Z V W b d hb hd) =
      ∑ x : genericPoints D₁, ∑ y : genericPoints D₂,
        (correspondenceExteriorComponentWeight X Y U V a c x *
          correspondenceExteriorComponentWeight Y Z V W b d y) •
          incidenceTorCorrespondence f g h
            (correspondenceExteriorComponentPoint X Y U V a c x)
            (correspondenceExteriorComponentPoint Y Z V W b d y)
            (correspondenceExteriorComponentPoint_admissible X Y U V a c ha hc x)
            (correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd y) := by
  classical
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  rw [correspondenceExteriorPrime_eq_sum_single X Y U V a c ha hc,
    correspondenceExteriorPrime_eq_sum_single Y Z V W b d hb hd]
  simp only [map_sum, AddMonoidHom.finsetSum_apply, incidenceTorPairing_single]
  rw [Finset.sum_comm]

/-- Product of the two genuine composites retains each original Tor weight and residue degree. -/
theorem correspondenceExterior_incidencePrimes_eq_sum :
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth
      X.hom Y.hom Z.hom a b hb).fintype
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth
      U.hom V.hom W.hom c d hd).fintype
    correspondenceExterior X Z U W
      (incidenceTorCorrespondence X.hom Y.hom Z.hom a b ha hb)
      (incidenceTorCorrespondence U.hom V.hom W.hom c d hc hd) =
      ∑ x : genericPoints I, ∑ y : genericPoints J,
        ((correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom a b x *
            ((qI).residueDegree x.val : ℤ)) *
          (correspondenceIncidenceTorCoefficient k U.hom V.hom W.hom c d y *
            ((qJ).residueDegree y.val : ℤ))) •
          correspondenceExteriorPrime X Z U W (qI x.val) (qJ y.val)
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
              X.hom Y.hom Z.hom a b ha hb x)
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
              U.hom V.hom W.hom c d hc hd y) := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    X.hom Y.hom Z.hom a b hb).fintype
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    U.hom V.hom W.hom c d hd).fintype
  rw [incidenceTorCorrespondence_eq_sum_single X.hom Y.hom Z.hom a b ha hb,
    incidenceTorCorrespondence_eq_sum_single U.hom V.hom W.hom c d hc hd]
  simp only [map_sum, AddMonoidHom.finsetSum_apply, correspondenceExterior_single]
  rw [Finset.sum_comm]

end Stacks.Chow
