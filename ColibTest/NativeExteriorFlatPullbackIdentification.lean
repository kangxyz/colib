/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.FlatPullbackIdentification

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "π" =>
  (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)
local notation3 (prettyPrint := false) "sB" => (pullback.fst X.hom Y.hom ≫ X.hom)
local notation3 (prettyPrint := false) "sBT" => (π ≫ sB)

example (z : (pullback X.hom Y.hom : Scheme))
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    (nativeExteriorPrime X Y T z hz).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (flatPullback C sBT sB π rfl (exteriorParameterDimension T)
          (relativeDimension_exteriorOuterProjection X Y T)
          (relativeDimension (C).dimensionFunction sB z)
          (pointCycleAtOwnDimension C sB z 1)).val :=
  nativeExteriorPrime_eq_diagonal_flatPullback X Y T z hz

example (n : ℤ) (α β : finiteCorrespondences X.hom Y.hom) :
    (nativeExterior X Y T (n • α - β)).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (nativeExteriorParameterPullback X Y T (n • α - β)) :=
  nativeExterior_eq_diagonal_parameterPullback X Y T (n • α - β)

example (n : ℤ) (α : finiteCorrespondences X.hom Y.hom)
    (hα : α.val ∈ cyclesOfDimension C sB n) :
    (nativeExterior X Y T α).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (flatPullback C sBT sB π rfl (exteriorParameterDimension T)
          (relativeDimension_exteriorOuterProjection X Y T) n ⟨α.val, hα⟩).val :=
  nativeExterior_eq_diagonal_flatPullback X Y T n α hα

#check exteriorSupportComapIso_hom_inclusion
#check exteriorOuterDiagonal_pullbackPoint
#check exteriorOuterDiagonal_pullbackPoint_residueDegree
#check nativeExteriorParameterPullback_single
#check nativeExterior_eq_diagonal_flatPullback_finsum
