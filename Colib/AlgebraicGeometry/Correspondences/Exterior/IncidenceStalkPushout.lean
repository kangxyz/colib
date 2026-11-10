/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingStalkFamily
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.LocalRingPushout

/-!
# The actual original and exterior incidence stalk pushout

SOURCE ONLY, UNCOMPILED. At an actual exterior incidence point, write C₀ and D
for the original and parameter-quotient coefficient stalks, and E₀ and E for
the original and exterior incidence stalks. The maps are α = q.stalkMap,
η = c.stalkMap and p = π.stalkMap. The map η₀ includes the saved stalkCongr
from q(c(x)) to b₀(π(x)); these points are not identified definitionally.

The same constructed ordered remaining-Y list generates both full incidence
kernels. Its literal image under α proves ker η = (ker η₀).map α. The actual
closed-immersion surjections and commuting stalk square therefore supply the
native algebra pushout. No arbitrary-stalk pullback theorem is assumed, and
no reduction, coefficient regularity or Tor comparison enters the argument.

Software reference: Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
StacksFrontier/AlgebraicGeometry/Perfect/DerivedStalk/LocalRingPushout.lean:90-93,151-164.
This specializes its public quotient-square theorem, not the derived-base-change
statement of Tag 0E23. The separate report gives the full actual map dictionary.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u v
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "E₀" => (I₀).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "E" => (I').presheaf.stalk x
local notation3 (prettyPrint := false) "α" => ((q).stalkMap (c x)).hom
local notation3 (prettyPrint := false) "η₀" =>
  (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom

/-- The actual ring-hom square retains the original incidence point transport. -/
theorem nativeExteriorRemainingIncidence_ringSquare :
    (p).comp η₀ = (η).comp α :=
  congrArg (fun f => f.hom)
    (nativeExteriorRemainingIncidence_stalkSquare X Y T z hz Z w hw x)

/-- The full exterior incidence kernel is the image of the full original kernel. -/
theorem nativeExteriorRemainingIncidence_kernel_image :
    RingHom.ker η = Ideal.map α (RingHom.ker η₀) := by
  let F := nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
  rw [F.coefficient_kernel, F.original_kernel, Ideal.map_ofList,
    F.coefficientList_eq_original_image]

/-- All five algebra structures and both towers are induced by the actual stalk maps. -/
theorem nativeExteriorIncidence_stalk_isPushout :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra C₀ E₀ := (η₀).toAlgebra
    let : Algebra C₀ E := ((η).comp α).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
      (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
    Algebra.IsPushout C₀ D E₀ E := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra C₀ E₀ := (η₀).toAlgebra
  let : Algebra C₀ E := ((η).comp α).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
    (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
  exact Algebra.IsPushout.symm
    (Stacks.Cohomology.StalkPushout.isPushout_of_surjective_of_ker
      (nativeExteriorRemainingOriginalIncidenceStalkMap_surjective X Y T z hz Z w hw x)
      ((c).stalkMap_surjective x)
      (nativeExteriorRemainingIncidence_kernel_image X Y Z T z w hz hw x))

end Stacks.Chow
