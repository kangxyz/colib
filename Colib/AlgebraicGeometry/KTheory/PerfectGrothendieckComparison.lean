/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import Colib.KTheory.Waldhausen.GrothendieckComparison.AsSmall

/-! # The original Waldhausen presentation of literal perfect-complex K₀

The original locally perfect complex model has distinct object and morphism
universes. The genuine universe bridge identifies its original weak-arrow and
cofibration-pushout Grothendieck presentation with its literal existing PerfectK.
This does not identify that presentation with a triangulated derived-category
presentation; that requires a separate triangle/cofibration comparison.
-/
@[expose] public section


open CategoryTheory.Waldhausen.AlgebraicGrothendieck


noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.AlgebraicGrothendieck

/-- The original locally perfect Waldhausen presentation computes the unchanged PerfectK₀. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckComparison.lean:33"
  "adaptation" "Original actual perfect K-zero comparison via native AsSmall"]
def perfectGrothendieckKZeroEquiv (X : Scheme.{u}) :
    Multiplicative (Group (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)) ≃*
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0 :=
  grothendieckKZeroEquivOfAsSmall (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)

/-- The literal original perfect-complex object class maps to its original topological loop. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckComparison.lean:38"
  "adaptation" "Original actual perfect K-zero comparison via native AsSmall", simp]
theorem perfectGrothendieckKZeroEquiv_objectClass (X : Scheme.{u}) (A :
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (objectClass (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        A)) =
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectClass A :=
  grothendieckKZeroEquivOfAsSmall_objectClass (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) A

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original open restriction respects every original classical perfect-complex class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckComparison.lean:47"
  "adaptation" "Original actual perfect K-zero comparison via native AsSmall"]
theorem perfectGrothendieckKZeroEquiv_restrict
    (a : Multiplicative (Group (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) :
    KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0 (perfectGrothendieckKZeroEquiv X a) =
      perfectGrothendieckKZeroEquiv U
        ((map (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
          (perfectComplexesRestrictOpenImmersion j)
          (perfectComplexesRestrictOpenImmersion_isExact j)).toMultiplicative a) :=
  grothendieckKZeroEquivOfAsSmall_natural (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectComplexesRestrictOpenImmersion j) (perfectComplexesRestrictOpenImmersion_isExact j) a

/-- The original open restriction is detected by the classical inverse on all literal PerfectK₀. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckComparison.lean:57"
  "adaptation" "Original actual perfect K-zero comparison via native AsSmall"]
theorem perfectGrothendieckKZeroEquiv_symm_restrict (x : (RingedSpace.perfectComplexesWaldhausen
  X.toRingedSpace).K 0) :
    (perfectGrothendieckKZeroEquiv U).symm (KMap (perfectComplexesRestrictOpenImmersion_isExact j)
      0 x) =
      (map (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectComplexesRestrictOpenImmersion j)
        (perfectComplexesRestrictOpenImmersion_isExact j)).toMultiplicative
          ((perfectGrothendieckKZeroEquiv X).symm x) :=
  grothendieckKZeroEquivOfAsSmall_symm_natural (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectComplexesRestrictOpenImmersion j) (perfectComplexesRestrictOpenImmersion_isExact j) x

end AlgebraicGeometry.Scheme.Modules
