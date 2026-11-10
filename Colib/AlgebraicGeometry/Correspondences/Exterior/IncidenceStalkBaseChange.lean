/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceStalkPushout

/-!
# Cancel base change along the actual incidence stalk pushout

SOURCE ONLY, UNCOMPILED. For any module M over the actual original incidence
stalk E₀, the canonical native comparison is E ⊗[E₀] M ≃ₗ[D] D ⊗[C₀] M.
The C₀ action on M is explicitly restriction along the point-transported η₀.
The E₀ and D actions on E are induced by p and η, respectively. The actual
commuting square provides both scalar towers used by Mathlib's cancellation.

Its inverse sends d ⊗ m to η(d) ⊗ m. Since η is surjective, these generators
determine the entire forward map as well. Both directions retain D-linearity.
There is no premise asserting a Tor isomorphism, length equality or pushout.

Software reference: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/RingTheory/IsTensorProduct.lean:777-819. Only its public
Algebra.IsPushout.cancelBaseChange and generator formulas are used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

open AlgebraicGeometry.Scheme

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

/-- Canonical cancellation for every actual original-incidence module. -/
def nativeExteriorIncidenceStalkBaseChange (M : Type v) [AddCommGroup M] [Module E₀ M] :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Module C₀ M := Module.compHom M η₀
    E ⊗[E₀] M ≃ₗ[D] D ⊗[C₀] M := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra C₀ E₀ := (η₀).toAlgebra
  let : Algebra C₀ E := ((η).comp α).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C₀ E₀ E := IsScalarTower.of_algebraMap_eq'
    (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x).symm
  let : Module C₀ M := Module.compHom M η₀
  have : IsScalarTower C₀ E₀ M := IsScalarTower.of_compHom C₀ E₀ M
  have : Algebra.IsPushout C₀ D E₀ E :=
    nativeExteriorIncidence_stalk_isPushout X Y Z T z w hz hw x
  exact Algebra.IsPushout.cancelBaseChange C₀ D E₀ E M

/-- The inverse is the actual quotient-map formula on every tensor generator. -/
@[simp]
theorem nativeExteriorIncidenceStalkBaseChange_symm_tmul
    (M : Type v) [AddCommGroup M] [Module E₀ M] (d : D) (m : M) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Module C₀ M := Module.compHom M η₀
    (nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M).symm
      (d ⊗ₜ[C₀] m) = (η) d ⊗ₜ[E₀] m := by
  simp [nativeExteriorIncidenceStalkBaseChange]
  rfl

/-- The forward map on an actual quotient-image generator; η is onto. -/
@[simp]
theorem nativeExteriorIncidenceStalkBaseChange_tmul
    (M : Type v) [AddCommGroup M] [Module E₀ M] (d : D) (m : M) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Module C₀ M := Module.compHom M η₀
    nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M
      ((η) d ⊗ₜ[E₀] m) = d ⊗ₜ[C₀] m := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Module C₀ M := Module.compHom M η₀
  rw [← nativeExteriorIncidenceStalkBaseChange_symm_tmul X Y Z T z w hz hw x M d m,
    LinearEquiv.apply_symm_apply]

/-- In particular, the comparison preserves the coefficient generator 1 ⊗ m. -/
@[simp]
theorem nativeExteriorIncidenceStalkBaseChange_one_tmul
    (M : Type v) [AddCommGroup M] [Module E₀ M] (m : M) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Module C₀ M := Module.compHom M η₀
    nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M
      (1 ⊗ₜ[E₀] m) = 1 ⊗ₜ[C₀] m := by
  simpa only [map_one] using
    nativeExteriorIncidenceStalkBaseChange_tmul X Y Z T z w hz hw x M 1 m

/-- The D action is the native left-factor action through the actual η on the source. -/
theorem nativeExteriorIncidenceStalkBaseChange_map_smul
    (M : Type v) [AddCommGroup M] [Module E₀ M] (d : D) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Module C₀ M := Module.compHom M η₀
    ∀ t : E ⊗[E₀] M,
      nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M (d • t) =
        d • nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M t := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Module C₀ M := Module.compHom M η₀
  dsimp only
  intro t
  exact (nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M).map_smul d t

/-- The inverse is D-linear with precisely the same coefficient map. -/
theorem nativeExteriorIncidenceStalkBaseChange_symm_map_smul
    (M : Type v) [AddCommGroup M] [Module E₀ M] (d : D) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let : Module C₀ M := Module.compHom M η₀
    ∀ t : D ⊗[C₀] M,
      (nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M).symm (d • t) =
        d • (nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M).symm t := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let : Module C₀ M := Module.compHom M η₀
  dsimp only
  intro t
  exact (nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M).symm.map_smul d t

end Stacks.Chow
