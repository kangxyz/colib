/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.OriginalTorKoszul
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceStalkBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingKoszulBaseChange

/-!
# Remaining coefficient homology and the actual original incidence Tor

At an arbitrary actual exterior incidence point x,
let C₀ and D be the original and parameter-quotient support stalks, and let E₀
and E be the original and exterior full-incidence stalks. Write α : C₀ → D,
η₀ : C₀ → E₀, η : D → E and p : E₀ → E for the actual saved stalk maps.
The native original ambient Tor T₀(n) has its existing E₀-module structure.
Its C₀-module structure is restriction along η₀, including the original-point cast.

The constructed remaining family F supplies the literal lists s₀ and sD.
Flat Koszul base change, the C₀-linear original Tor comparison, and cancellation
in the actual stalk pushout give H_n(K(sD; D)) ≃ₗ[D] E ⊗[E₀] T₀(n).
The tensor product uses p.toAlgebra, and D acts through η on its E factor.
No comparison, regularity of a coefficient list, or Tor vanishing is an input.

The flat homology provider gives Nonempty. We choose one witness and use it
consistently below; no canonical or choice-independent homology map is claimed.
The generator formula specifies the remaining tensor and cancellation steps.
This file makes no assertion that the leading ambient Tor comparison is D-linear.

Software: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/LinearAlgebra/TensorProduct/Tower.lean:727-744 and
Mathlib/RingTheory/IsTensorProduct.lean:777-819. The flat Koszul ingredient is
Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
StacksFrontier/RingTheory/Koszul/FlatBaseChange.lean:565-573.
These are ingredients, not literature attributions of this geometric assembly.
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
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)
local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "H₀" =>
  Koszul.seqComplexTensor (F).originalCoefficientList.get (ModuleCat.of C₀ C₀)
local notation3 (prettyPrint := false) "HD" =>
  Koszul.seqComplexTensor (F).coefficientList.get (ModuleCat.of D D)

/-- Choose one actual flat Koszul comparison, with the literal constructed lists. -/
def nativeExteriorRemainingKoszulHomologyBaseChangeEquiv (n : ℕ) :
    let : Algebra C₀ D := (α).toAlgebra
    (HD).homology n ≃ₗ[D] D ⊗[C₀] (H₀).homology n :=
  Classical.choice
    (nativeExteriorRemainingCoefficient_list_homology_baseChange X Y Z T z w hz hw x n)

/-- Remaining coefficient homology is the actual incidence base change of original native Tor.
The D action on the target is through c.stalkMap, and the E₀ action uses π.stalkMap. -/
def nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv (n : ℕ) :
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    (HD).homology n ≃ₗ[D] E ⊗[E₀] T₀ n := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  exact (nativeExteriorRemainingKoszulHomologyBaseChangeEquiv X Y Z T z w hz hw x n).trans
    (((nativeExteriorOriginalTorRemainingKoszulEquiv
      X Y Z T z w hz hw x n).symm.baseChange C₀ D _ _).trans
        (nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x (T₀ n)).symm)

/-- After the selected flat comparison, the actual quotient sends d ⊗ t to η(d) ⊗ t.
This formula specifies the tensor stage without asserting a canonical flat homology choice. -/
theorem nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv_tmul
    (n : ℕ) (d : D) (t : T₀ n) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv X Y Z T z w hz hw x n
      ((nativeExteriorRemainingKoszulHomologyBaseChangeEquiv X Y Z T z w hz hw x n).symm
        (d ⊗ₜ[C₀]
          nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n t)) =
      (η) d ⊗ₜ[E₀] t := by
  let : Algebra C₀ D := (α).toAlgebra
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  simp only [nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.symm_apply_apply, nativeExteriorIncidenceStalkBaseChange_symm_tmul]

end Stacks.Chow
