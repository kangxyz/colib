/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceStalkPushout

/-!
SOURCE ONLY, UNCOMPILED. The native algebra tensor product is evaluated at an
actual exterior incidence point. Its generator formula uses η and p, while
the full kernel calculation uses the very same constructed ordered Y family.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open AlgebraicGeometry.Scheme
open scoped TensorProduct

noncomputable section
universe u
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

-- Actual quotient kernels, with no reduced-incidence substitute.
example : RingHom.ker η = Ideal.map α (RingHom.ker η₀) :=
  nativeExteriorRemainingIncidence_kernel_image X Y Z T z w hz hw x

-- The square gives a native algebra equivalence, not a caller-supplied provider.
example :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra C₀ E₀ := (η₀).toAlgebra
    let : Algebra C₀ E := ((η).comp α).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
      (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
    have : Algebra.IsPushout C₀ D E₀ E :=
      nativeExteriorIncidence_stalk_isPushout X Y Z T z w hz hw x
    Nonempty (D ⊗[C₀] E₀ ≃ₐ[D] E) := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra C₀ E₀ := (η₀).toAlgebra
  let : Algebra C₀ E := ((η).comp α).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
    (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
  have : Algebra.IsPushout C₀ D E₀ E :=
    nativeExteriorIncidence_stalk_isPushout X Y Z T z w hz hw x
  exact ⟨Algebra.IsPushout.equiv C₀ D E₀ E⟩

-- Its multiplication formula retains both actual local-ring maps.
example (d : D) (e₀ : E₀) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra C₀ E₀ := (η₀).toAlgebra
    let : Algebra C₀ E := ((η).comp α).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
      (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
    have : Algebra.IsPushout C₀ D E₀ E :=
      nativeExteriorIncidence_stalk_isPushout X Y Z T z w hz hw x
    Algebra.IsPushout.equiv C₀ D E₀ E (d ⊗ₜ[C₀] e₀) = (η) d * (p) e₀ := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra C₀ E₀ := (η₀).toAlgebra
  let : Algebra C₀ E := ((η).comp α).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
    (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
  have : Algebra.IsPushout C₀ D E₀ E :=
    nativeExteriorIncidence_stalk_isPushout X Y Z T z w hz hw x
  exact Algebra.IsPushout.equiv_tmul C₀ D E₀ E d e₀

-- Original coefficient elements have the same image by the actual point-cast square.
example (a : C₀) : (p) ((η₀) a) = (η) ((α) a) :=
  RingHom.congr_fun (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x) a
