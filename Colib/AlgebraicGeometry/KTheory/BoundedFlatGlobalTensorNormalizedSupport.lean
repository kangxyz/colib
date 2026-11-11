/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorUnitNormalization
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterOpenTrack

/-! The actual supported lift and forget map retain the genuine tensor-unitor normalization. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack

/-- Normalize genuine tensor multiplication at the actual parameter product scheme. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:22"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
def ambientUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  globalNormalizedTensorUnit
    ((baseProductFunctor (specULiftZIsTerminal.from Q)).op.obj (laurent.op.obj X))
    (projectedLaurentScalar Q X)

/-- The entire normalized ambient unit is the existing parameter unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:28"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem ambientUnit_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ambientUnit Q X = ParameterLaurentUnit.ambientUnit Q X :=
  globalNormalizedTensorUnit_eq _ _

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- Lift the genuine normalized unit through the actual supported full-subcategory inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:35"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
def supportedUnit (X : Scheme.{u}ᵒᵖ) :=
  lift (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X)

/-- The actual supported lift agrees with the existing original supported unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:39"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem supportedUnit_eq (X : Scheme.{u}ᵒᵖ) :
    supportedUnit f X = ParameterLaurentTrack.supportedUnit f X := by
  unfold supportedUnit
  rw [ambientUnit_eq]
  rfl

/-- Support forget preserves the normalized tensor automorphisms on every object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:46"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem forget_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.forget f).app (laurent.op.obj X)).hom.toFunctor
      (supportedUnit f X) (ambientUnit Q X) := by
  rw [supportedUnit_eq, ambientUnit_eq]
  exact ParameterLaurentTrack.forget_unit f X

/-- Original supported pullback preserves the same genuine normalized unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:53"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem supportedUnit_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.supported f).map (laurent.op.map g)).hom.toFunctor
      (supportedUnit f X) (supportedUnit f Y) := by
  rw [supportedUnit_eq, supportedUnit_eq]
  exact ParameterLaurentTrack.supportedUnit_naturality f g

/-- The actual full-open restriction retains the same normalized parameter unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorNormalizedSupport.lean:60"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem openRestriction_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.openRestriction f).app (laurent.op.obj X)).hom.toFunctor
      (ParameterLaurentTrack.openUnit f X) (ambientUnit P X) := by
  rw [ambientUnit_eq]
  exact ParameterLaurentTrack.openRestriction_unit f X

end AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport

namespace AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport

attribute [colib_tag "COL-0560"] supportedUnit_naturality

end AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport
