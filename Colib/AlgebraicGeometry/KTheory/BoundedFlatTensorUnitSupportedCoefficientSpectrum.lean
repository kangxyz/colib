/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallModel
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallCylinder
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationSpectrum

/-!
# The genuine supported tensor coefficient cell in its row spectrum

All objects and structure maps use the original supported Waldhausen category. The independently
constructed first tensor row agrees, as a whole double cylinder, with the finite transformation
row construction. Its realization retains the separate row, unit-edge and zero-level loop times.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T) (r : (Γ(S.right, ⊤))ˣ)

/-- The original exact supported tensor-pullback prespectrum map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:31"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorSupportedPairPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen T.hom)
    (boundedAboveFlatPerfectSupportedWaldhausen S.hom) (tensorSupportedPair_exact p)

/-- The original forward tensor coefficient acts within the supported target. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:36"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorSupportedPairHomotopy :
    Homotopy (tensorSupportedPairPrespectrumMap p) (tensorSupportedPairPrespectrumMap p) :=
  exactOriginalPrespectrumIsoHomotopy (boundedAboveFlatPerfectSupportedWaldhausen T.hom)
    (boundedAboveFlatPerfectSupportedWaldhausen S.hom)
    (tensorSupportedPair_exact p) (tensorSupportedPair_exact p)
    (tensorSupportedPairAutomorphism p r)

/-- Its small-model formula retains the original selected-zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:44"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorSupportedPairHomotopy_model :
    tensorSupportedPairHomotopy p r =
      prespectrumTransformationHomotopy (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) := rfl

/-- Finite S-prolongation of the actual supported row transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:50"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorSupportedPairCoefficientStageCylinder (k : ℕ) :=
  rowTransformationCylinder (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) k

/-- At the first row this is the independently constructed genuine tensor coefficient cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:55"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorSupportedPairCoefficientStageCylinder_zero :
    tensorSupportedPairCoefficientStageCylinder p r 0 =
      tensorSupportedPairSmallCoefficientCylinder p r :=
  (tensorSupportedPairSmallCoefficientCylinder_row p r).symm

/-- Whole realization with the original two cylinder isomorphisms, row time outermost. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:61"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorSupportedPairCoefficientStageRealization (k : ℕ) :=
  rowTransformationRealization (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) k

/-- The complete supported row-spectrum homotopy. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:66"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorSupportedPairCoefficientSpectrumHomotopy :
    Homotopy
      (tensorSupportedPairPrespectrumMap p ≫
        rowStabilizationMap (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen
          S.hom)))
      (tensorSupportedPairPrespectrumMap p ≫
        rowStabilizationMap (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen
          S.hom))) :=
  (tensorSupportedPairHomotopy p r).postcomp
    (rowStabilizationMap (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom)))

/-- Every positive level is exactly the realized supported double cylinder. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:76"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorSupportedPairCoefficientSpectrumHomotopy_succ
    (k : ℕ) (t s : unitInterval)
    (x : stageSpace k (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen T.hom))) :
    Path.toContinuousMap
      ((tensorSupportedPairCoefficientSpectrumHomotopy p r).level (k + 1) (t, x)) s =
      tensorSupportedPairCoefficientStageRealization p r k (s, (t, x)) :=
  rowTransformationSpectrumHomotopy_succ (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) k t s x

/-- The original zero extension keeps input-loop time independent from both coefficient times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSp\
    ectrum.lean:86"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorSupportedPairCoefficientSpectrumHomotopy_zero (t a s : unitInterval)
    (γ : Path (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen
      T.hom)))
      (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen T.hom)))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((tensorSupportedPairCoefficientSpectrumHomotopy p r).level 0 (t, γ)) a) s =
      tensorSupportedPairCoefficientStageRealization p r 0 (s, (t, γ a)) :=
  rowTransformationSpectrumHomotopy_zero (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) t a s γ

end AlgebraicGeometry.Scheme.Modules
