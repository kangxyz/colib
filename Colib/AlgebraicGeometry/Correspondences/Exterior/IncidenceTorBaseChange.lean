/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientTorKoszul
public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingTorBaseChange
public import Mathlib.Algebra.Algebra.Basic

/-!
# Native incidence-linear exterior Tor base change

Let k be any field, let X, Y, Z, T be smooth-site
objects over k, and assume T geometrically integral. For actual finite
correspondence points z, w and any point x of the full native exterior incidence,
write π for its actual projection to the original incidence. In every degree n,
including zero, this file constructs T'(n) ≃ₗ[E] E ⊗[E₀] T₀(n).
Here E is the full exterior incidence stalk at x, E₀ is the full original
incidence stalk at π(x), and both Tors are the existing native ambient Tors.
Both incidence actions are exactly correspondenceIncidenceTorModule. The
tensor product uses the actual algebra (π.stalkMap x).hom.toAlgebra.

The leading-block reduction is only R-linear for the actual native ambient
stalk R. The remaining comparison is D-linear. Its scalar restriction agrees
with the target's R action because η.comp κ is the actual ambient-to-E map.
Compose these R-linear equivalences and use the surjectivity of that map and
the existing native Tor scalar tower to extend scalars to E. No D-linearity of
the leading reduction is used. No comparison, support-flatness, coefficient
regularity, vanishing, reducedness, perfection or genericity is a caller premise.

Choices in the regular families and the Nonempty flat homology comparison are
retained. The construction asserts an equivalence with its actual scalar
linearity, not canonical chain-level naturality or independence of those choices.
Length, Euler-coefficient, cycle and pushforward conclusions are not asserted.

Software: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Algebra/Basic.lean:580-593 supplies the surjective scalar extension.
The native action and its tower are the existing Colib provider
Colib/AlgebraicGeometry/Correspondences/Composition/PairTorAction.lean:113-158
at e7697ab8164435c7093665d02ac34f021eefb75e. No new Stacks tag is assigned
to the complete assembly. Exact inputs and the full mathematical proof are
recorded in the separate mathematical report.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "a" =>
  correspondenceIncidenceAmbientInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "R" =>
  correspondenceIncidenceAmbientStalk fX fY fZ z' w' x
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "E₀" => (I₀).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "E" => (I').presheaf.stalk x
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom
local notation3 (prettyPrint := false) "κ" =>
  nativeExteriorTorCoefficientStalkMap X Y Z T z w hz hw x
local notation3 (prettyPrint := false) "T'" =>
  correspondenceIncidenceAmbientTor fX fY fZ z' w' x
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)

/-- The coefficient route acts on the actual tensor target through the native ambient quotient. -/
theorem nativeExteriorIncidenceTensor_coefficient_smul (n : ℕ) (r : R) :
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    ∀ m : E ⊗[E₀] T₀ n, (κ) r • m = ((a).stalkMap x).hom r • m := by
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  dsimp only
  intro m
  calc
    (κ) r • m = (η) ((κ) r) • m := (IsScalarTower.algebraMap_smul E _ _).symm
    _ = ((a).stalkMap x).hom r • m := congrArg (fun s : E => s • m)
      (RingHom.congr_fun
        (nativeExteriorTorCoefficientStalkMap_incidence X Y Z T z w hz hw x) r)

/-- Compose the native ambient reduction and actual coefficient base change over R.
The target R action is induced by the native ambient-to-incidence stalk map itself. -/
def nativeExteriorAmbientTorIncidenceBaseChangeEquiv (n : ℕ) :
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra R E := ((a).stalkMap x).hom.toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    T' n ≃ₗ[R] E ⊗[E₀] T₀ n := by
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra R E := ((a).stalkMap x).hom.toAlgebra
  let : Algebra D E := (η).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let eK := (nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).toLinearEquiv
  let eD := nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv X Y Z T z w hz hw x n
  refine { eK.toAddEquiv.trans eD.toAddEquiv with map_smul' := ?_ }
  intro r m
  change eD (eK (r • m)) = r • eD (eK m)
  have hK : eK (r • m) = (κ) r • eK m := eK.map_smul r m
  rw [hK, eD.map_smul]
  exact (nativeExteriorIncidenceTensor_coefficient_smul X Y Z T z w hz hw x n r _).trans
    (IsScalarTower.algebraMap_smul E r _)

/-- Every native exterior Tor degree is incidence-linearly the actual base change of
original native Tor, with both pre-existing incidence actions and π.stalkMap on scalars. -/
def nativeExteriorIncidenceTorBaseChangeEquiv (n : ℕ) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    T' n ≃ₗ[E] E ⊗[E₀] T₀ n := by
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra R E := ((a).stalkMap x).hom.toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
  have : IsScalarTower R E (T' n) :=
    correspondenceIncidenceTorScalarTower fX fY fZ z' w' x n
  exact LinearEquiv.extendScalarsOfSurjective («R» := R) (S := E)
    ((a).stalkMap_surjective x)
    (nativeExteriorAmbientTorIncidenceBaseChangeEquiv X Y Z T z w hz hw x n)

/-- An arbitrary actual incidence scalar acts through the existing native Tor action. -/
theorem nativeExteriorIncidenceTorBaseChangeEquiv_map_smul
    (n : ℕ) (e : E) (t : T' n) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n (e • t) =
      e • nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n t := by
  let : Algebra E₀ E := (p).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
  exact (nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n).map_smul e t

/-- The incidence-linear equivalence also has the original native ambient scalar formula. -/
theorem nativeExteriorIncidenceTorBaseChangeEquiv_ambient_smul
    (n : ℕ) (r : R) (t : T' n) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n (r • t) =
      ((a).stalkMap x).hom r •
        nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n t := by
  let : Algebra E₀ E := (p).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
  dsimp only
  rw [← correspondenceIncidenceTorModule_stalkMap_smul fX fY fZ z' w' x n r t]
  exact (nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n).map_smul _ t

end Stacks.Chow
