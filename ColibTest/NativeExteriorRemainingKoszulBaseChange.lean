/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingKoszulBaseChange

/-!
SOURCE ONLY, UNCOMPILED. The lists come from the constructed family at the
actual exterior incidence point. Both coefficient modules are the full stalk
rings. The examples keep all homological degrees and use no regularity or
vanishing premise for either coefficient list.
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

local notation3 "F" => nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 "s₀" => (F).originalCoefficientList
local notation3 "sD" => (F).coefficientList

-- The common tuple generates precisely the full exterior incidence kernel.
example : Ideal.ofList (List.ofFn (fun j => (α) ((s₀).get j))) = RingHom.ker η := by
  rw [nativeExteriorRemainingCoefficient_ofFn, ← (F).coefficient_kernel]

-- A comparison exists in every degree, with the literal actual exterior list.
example (n : ℕ) :
    let : Algebra C₀ D := (α).toAlgebra
    Nonempty
      (((Koszul.seqComplexTensor (sD).get D).homology n) ≃ₗ[D]
        (D ⊗[C₀] ((Koszul.seqComplexTensor (s₀).get C₀).homology n))) :=
  nativeExteriorRemainingCoefficient_list_homology_baseChange X Y Z T z w hz hw x n

-- Degree zero is included; reversing the existence assertion makes no canonical-choice claim.
example :
    let : Algebra C₀ D := (α).toAlgebra
    Nonempty ((D ⊗[C₀] ((Koszul.seqComplexTensor (s₀).get C₀).homology 0)) ≃ₗ[D]
      ((Koszul.seqComplexTensor (sD).get D).homology 0)) := by
  let : Algebra C₀ D := (α).toAlgebra
  obtain ⟨e⟩ :=
    nativeExteriorRemainingCoefficient_list_homology_baseChange X Y Z T z w hz hw x 0
  exact ⟨e.symm⟩

-- The actual tensor unit removes only the coefficient tensor factor.
example (d : D) (a : C₀) :
    let : Algebra C₀ D := (α).toAlgebra
    TensorProduct.AlgebraTensorModule.rid C₀ D D (d ⊗ₜ[C₀] a) = (α) a * d :=
  nativeExteriorRemainingCoefficient_tensorUnit_tmul X Y Z T z w hz hw x d a
