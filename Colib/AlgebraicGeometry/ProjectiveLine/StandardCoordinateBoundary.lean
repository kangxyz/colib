/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateBoundaryFormula
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalSurjectivity

/-! # The first projective-line coordinate of the actual inverse unit -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

local notation "PL" S => projectiveSpaceOver 1 S
local notation "WK" S => RingedSpace.perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace S))

/-- The first coordinate of the boundary of the original inverse unit is the coefficient. -/
theorem firstCoordinate_connectingHom_inverseCoordinateUnit (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ)
    (a : (WK(X.obj)).K n) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let q := (overlapCoordinateUnit X)⁻¹
    ((projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
        (originalKSelfTrackOperation (WK((negativeChart X.obj).toScheme))
          (WK((j ⁻¹ᵁ T).toScheme))
          (perfectFlatUnitHomotopy (j ⁻¹ᵁ T).ι q) n
          (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
            (KMap (projectiveLineFirstSummand_exact X.obj) n a))))).1 = a := by
  have h := connectingHom_inverseCoordinateUnit X n a
  have hc := congrArg (fun z => ((projectiveLineKEquiv X.obj n).symm z).1) h
  exact hc.trans (congrArg Prod.fst ((projectiveLineKEquiv X.obj n).symm_apply_apply (a, a⁻¹)))

end AlgebraicGeometry.Scheme.ProjectiveLine
