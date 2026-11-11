/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Composition
import Colib.AlgebraicGeometry.Correspondences.Exterior.Graph

/-!
# Actual prime, signed, finite-sum, and identity-graph composition consumers

Every example applies the comparison to the existing native exterior and
incidence Tor operations. The signed finite families have no distinctness or
injectivity hypothesis, so repeated prime cycles and cancelling coefficients
are allowed. Identities below are the existing full componentwise diagonal
graphs, not formal generators supplied with unit axioms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme
open scoped BigOperators

universe u v v'

namespace NativeExteriorCompositionTest

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom

section PrimePairs

variable (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

example :
    nativeExterior X Z T (incidenceTorCorrespondence X.hom Y.hom Z.hom z w hz hw) =
      incidenceTorCorrespondence fX fY fZ
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
        (nativeExteriorPoint_admissible X Y T z hz)
        (nativeExteriorPoint_admissible Y Z T w hw) :=
  nativeExterior_incidenceTorCorrespondence X Y Z T z w hz hw

-- The two original coefficients multiply with their actual signs.
example :
    nativeExterior X Z T
      (incidenceTorPairing X.hom Y.hom Z.hom
        (singleFiniteCorrespondence X.hom Y.hom z hz (-3))
        (singleFiniteCorrespondence Y.hom Z.hom w hw 2)) =
      ((-3 : ℤ) * 2) • incidenceTorCorrespondence fX fY fZ
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
        (nativeExteriorPoint_admissible X Y T z hz)
        (nativeExteriorPoint_admissible Y Z T w hw) := by
  rw [incidenceTorPairing_single, map_zsmul, nativeExterior_incidenceTorCorrespondence]

end PrimePairs

section SignedCycles

variable (α α' : finiteCorrespondences X.hom Y.hom)
  (β : finiteCorrespondences Y.hom Z.hom)

example :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom α β) =
      incidenceTorPairing fX fY fZ (nativeExterior X Y T α) (nativeExterior Y Z T β) :=
  nativeExterior_incidenceTorPairing X Y Z T α β

example :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom (-α) β) =
      -incidenceTorPairing fX fY fZ (nativeExterior X Y T α) (nativeExterior Y Z T β) := by
  rw [nativeExterior_incidenceTorPairing, map_neg, incidenceTorPairing_neg_left]

example :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom 0 β) = 0 := by
  rw [nativeExterior_incidenceTorPairing, map_zero, incidenceTorPairing_zero_left]

example :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom α 0) = 0 := by
  rw [nativeExterior_incidenceTorPairing, map_zero, incidenceTorPairing_zero_right]

example :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom (α - α') β) =
      incidenceTorPairing fX fY fZ (nativeExterior X Y T α) (nativeExterior Y Z T β) -
        incidenceTorPairing fX fY fZ (nativeExterior X Y T α') (nativeExterior Y Z T β) := by
  rw [nativeExterior_incidenceTorPairing, map_sub, incidenceTorPairing_sub_left]

-- Repeated equal cycles with opposite coefficients cancel after actual composition.
example :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom (α - α) β) = 0 := by
  rw [nativeExterior_incidenceTorPairing, map_sub, sub_self, incidenceTorPairing_zero_left]

end SignedCycles

-- There is no injectivity premise on either family, nor a sign restriction on m or n.
example {ι : Type v} {κ : Type v'} (s : Finset ι) (t : Finset κ)
    (α : ι → finiteCorrespondences X.hom Y.hom)
    (β : κ → finiteCorrespondences Y.hom Z.hom) (m : ι → ℤ) (n : κ → ℤ) :
    nativeExterior X Z T
      (incidenceTorPairing X.hom Y.hom Z.hom (∑ i ∈ s, m i • α i) (∑ j ∈ t, n j • β j)) =
      incidenceTorPairing fX fY fZ
        (∑ i ∈ s, m i • nativeExterior X Y T (α i))
        (∑ j ∈ t, n j • nativeExterior Y Z T (β j)) := by
  rw [nativeExterior_incidenceTorPairing]
  simp only [map_sum, map_zsmul]

-- This is the existing full graph of id_X, including all source components.
example :
    nativeExterior X X T
      (incidenceTorPairing X.hom X.hom X.hom
        ((Cor.graphFunctor k).map (𝟙 X)) ((Cor.graphFunctor k).map (𝟙 X))) =
      𝟙 (Cor.mk (SmoothSite.product X T)) := by
  have hid : ((Cor.graphFunctor k).map (𝟙 X) : finiteCorrespondences X.hom X.hom) =
      𝟙 (Cor.mk X) := (Cor.graphFunctor k).map_id X
  rw [hid, nativeExterior_incidenceTorPairing, nativeExterior_id]
  change (𝟙 (Cor.mk (SmoothSite.product X T))) ≫ 𝟙 _ = _
  exact Category.id_comp _

example (α : finiteCorrespondences X.hom Y.hom) :
    nativeExterior X Y T
      (incidenceTorPairing X.hom X.hom Y.hom (𝟙 (Cor.mk X)) α) =
      nativeExterior X Y T α := by
  rw [nativeExterior_incidenceTorPairing, nativeExterior_id]
  change (𝟙 (Cor.mk (SmoothSite.product X T))) ≫ nativeExterior X Y T α = _
  exact Category.id_comp _

example (α : finiteCorrespondences X.hom Y.hom) :
    nativeExterior X Y T
      (incidenceTorPairing X.hom Y.hom Y.hom α (𝟙 (Cor.mk Y))) =
      nativeExterior X Y T α := by
  rw [nativeExterior_incidenceTorPairing, nativeExterior_id]
  change nativeExterior X Y T α ≫ 𝟙 (Cor.mk (SmoothSite.product Y T)) = _
  exact Category.comp_id _

end NativeExteriorCompositionTest
