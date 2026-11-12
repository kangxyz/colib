/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedInputStable
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorNormalizedRowPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEmptySupportedParameterModels

/-!
# The actual support-forgetful map of normalized row presentations

The original Model inclusion and its actual projected Laurent-unit square define
the normalized input map. For an empty open source, the genuine Model isomorphism
makes this same map a stable equivalence. The original current comparison square
retains the full normalization homotopy.
-/
@[expose] public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedRowPresentation
open GlobalSupportedSection GlobalSectionChangeIndex ParameterLaurentTrack ParameterLaurentUnit
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original support inclusion acts on both actual legs of the normalized presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedRowForget.lean:35"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def forget (X : Scheme.{u}ᵒᵖ) : supported f X ⟶ ambient Q X :=
  SchemeModelRowSeed.normalizedInputMap (ParameterModels.supported f)
    (supportedUnit f) (supportedUnit_naturality f)
    (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
    (ParameterModels.forget f) (forget_unit f) X

/-- The actual current forgetful map and the entire normalization comparison commute. -/
@[reassoc, colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedRowForget.lean:43"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem current_forget_square (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentInputMap (supportedTrack f) (ambientTrack Q)
      (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
      (forget_equivariant f)).app X ≫ ambientComparison Q X =
      supportedComparison f X ≫ forget f X :=
  SchemeModelRowSeed.normalizedComparison_inputMap (ParameterModels.supported f)
    (supportedUnit f) (supportedUnit_naturality f)
    (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
    (ParameterModels.forget f) (forget_unit f) X

/-- Every original nonnegative Model class, including zero, retains its exact forget map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedRowForget.lean:54"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem modelClass_forget (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : ((ParameterModels.supported f).obj X).obj.waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (forget f X)
      (SchemeModelRowSeed.normalizedModelClass (ParameterModels.supported f)
        (supportedUnit f) (supportedUnit_naturality f) X n x) =
    SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient Q)
      (ambientUnit Q) (ambientUnit_naturality Q) X n
      (CategoryTheory.Waldhausen.KMap ((ParameterModels.forget f).app X).hom.isExact n x) := by
  have h := congrArg (stableHomotopyFunctor (n : ℤ)).map
    (SchemeModelRowSeed.normalizedStageInclusion_input
      (ParameterModels.supported f) (supportedUnit f) (supportedUnit_naturality f)
      (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
      (ParameterModels.forget f) (forget_unit f) X 0)
  simp only [Functor.map_comp] at h
  have hv := ConcreteCategory.congr_hom h
    (smallModelKStableEquiv ((ParameterModels.supported f).obj X) n (Additive.ofMul x))
  unfold SchemeModelRowSeed.normalizedModelClass
  exact hv.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      (SchemeModelRowSeed.normalizedStageInclusion (ParameterModels.ambient Q)
        (ambientUnit Q) (ambientUnit_naturality Q) X 0))
    (smallModelKStableEquiv_naturality ((ParameterModels.forget f).app X) n x).symm)

/-- Empty-open support is forgotten by a stable equivalence of the actual normalized rows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedRowForget.lean:78"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem forget_stable_of_isEmpty [IsEmpty P] (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (forget f X) := by
  have : IsIso (ParameterModels.forget f) := by
    rw [← ParameterModels.emptySupportedIso_hom f]
    infer_instance
  exact SchemeModelRowSeed.normalizedInputMap_stable_of_isIso
    (ParameterModels.supported f) (supportedUnit f) (supportedUnit_naturality f)
    (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
    (ParameterModels.forget f) (forget_unit f) X

/-- The bottom-open specialization keeps the original support-forgetful presentation map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedRowForget.lean:89"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem bottom_forget_stable (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (forget (⊥ : Q.Opens).ι X) :=
  forget_stable_of_isEmpty (⊥ : Q.Opens).ι X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedRowPresentation
