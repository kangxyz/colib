/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorNormalizedSupport

/-! Whole parameter tracks from the actual normalized tensor units on the original Models. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedTrack
open GlobalSectionChangeIndex GlobalTensorNormalizedSupport GlobalSupportedSection NaturalTrack

private theorem units_track_congr (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1})
    (α β : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
    (hα : ∀ {X Y} (g : X ⟶ Y),
      Preserves (M.map (laurent.op.map g)).hom.toFunctor (α X) (α Y))
    (hβ : ∀ {X Y} (g : X ⟶ Y),
      Preserves (M.map (laurent.op.map g)).hom.toFunctor (β X) (β Y)) (h : α = β) :
    ofModelUnits laurent.op coefficient M α hα =
      ofModelUnits laurent.op coefficient M β hβ := by
  subst β
  rfl

/-- Actual parameter pullback preserves the normalized genuine ambient tensor unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedTrack.lean:33"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem ambientUnit_naturality (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.ambient Q).map (laurent.op.map g)).hom.toFunctor
      (ambientUnit Q X) (ambientUnit Q Y) := by
  rw [ambientUnit_eq, ambientUnit_eq]
  exact ParameterLaurentUnit.ambientUnit_naturality Q g

/-- The normalized genuine tensor unit induces the actual ambient parameter track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedTrack.lean:40"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
def ambientTrack (Q : Scheme.{u}) :
    Track laurent.op coefficient (ParameterModels.ambient Q ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
    (ambientUnit Q) (ambientUnit_naturality Q)

/-- The entire ambient track is the original parameter track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedTrack.lean:46"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem ambientTrack_eq (Q : Scheme.{u}) :
    ambientTrack Q = ParameterLaurentTrack.ambientTrack Q := by
  have h : ambientUnit Q = ParameterLaurentUnit.ambientUnit Q := funext (ambientUnit_eq Q)
  unfold ambientTrack ParameterLaurentTrack.ambientTrack
  congr

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual supported lift of normalized tensor multiplication induces this track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedTrack.lean:55"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
def supportedTrack :
    Track laurent.op coefficient (ParameterModels.supported f ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.supported f)
    (supportedUnit f) (supportedUnit_naturality f)

/-- The entire supported track retains the original support predicate and every time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedTrack.lean:61"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem supportedTrack_eq : supportedTrack f = ParameterLaurentTrack.supportedTrack f := by
  have h : supportedUnit f = ParameterLaurentTrack.supportedUnit f :=
    funext (supportedUnit_eq f)
  exact units_track_congr (ParameterModels.supported f) _ _
    (supportedUnit_naturality f) (ParameterLaurentTrack.supportedUnit_naturality f) h

end AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedTrack
