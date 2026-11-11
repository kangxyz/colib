/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientSmallModel
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationCylinder

/-!
# Finite S-prolongation of the genuine first tensor coefficient cell

Apply the original finite S-construction to the actual normalized coefficient-row arrow. The
first-row insertion is kept after the tensor pullback, and the forward unit edge is prolonged
entrywise through the original quotient grids. At stage zero the whole cell is the independent
raw tensor construction, transported by the original small-model maps. At every stage its whole
simplicial map equals the original tensor cylinder followed by the original structure cylinder.
The two interval directions are never interchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Apply the genuine finite S-construction to the normalized first-row tensor arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStages.lean:34"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
def tensorUnitPullbackCoefficientStageSimplex (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj n)
    (τ θ : (Δ[1]).obj n) :
    ((stages (k + 1)).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace))).obj n :=
  stageTransformationFunction k
    (F := tensorUnitPullbackModelMap f ≫
      (insertion θ.down).app (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
    (G := tensorUnitPullbackModelMap f ≫
      (insertion θ.down).app (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
    (whiskerRight (tensorUnitPullbackModelTransformation f r)
      ((insertion θ.down).app (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace))).hom.toFunctor)
    (fun B => ((insertion θ.down).app (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace))).hom.isExact.weak _
      (tensorUnitPullbackModelTransformation_weak f r B)) n A τ

/-- Entrywise finite S-prolongation preserves the whole tensor-arrow/first-row composite. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStages.lean:49"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
theorem tensorUnitPullbackCoefficientStageSimplex_eq (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj n)
    (τ θ : (Δ[1]).obj n) :
    tensorUnitPullbackCoefficientStageSimplex f r k n A τ θ =
      (stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).app n
        (stageTransformationFunction k (tensorUnitPullbackModelTransformation f r)
          (tensorUnitPullbackModelTransformation_weak f r) n A τ, θ) :=
  stageTransformationFunction_postcomp k (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r)
    ((insertion θ.down).app (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      n A τ

/-- The actual finite coefficient cells assemble under all diagonal simplicial operators. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStages.lean:61"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
def tensorUnitPullbackCoefficientStageCylinder (k : ℕ) :
    (((stages k).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))) ⊗
      Δ[1]) ⊗ Δ[1] ⟶
      (stages (k + 1)).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  rowTransformationCylinder (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r) k

/-- This is a whole simplicial-map identity, not an equality merely on homotopy classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStages.lean:68"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
theorem tensorUnitPullbackCoefficientStageCylinder_eq (k : ℕ) :
    tensorUnitPullbackCoefficientStageCylinder f r k =
      (stageTransformationCylinder k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) ▷ Δ[1]) ≫
        stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact tensorUnitPullbackCoefficientStageSimplex_eq f r k n z.1.1 z.1.2 z.2

/-- The starting cell is exactly the independently constructed genuine coefficient tensor row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStages.lean:80"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
theorem tensorUnitPullbackCoefficientStageCylinder_zero :
    tensorUnitPullbackCoefficientStageCylinder f r 0 =
      tensorUnitPullbackSmallCoefficientCylinder f r := by
  rw [tensorUnitPullbackCoefficientStageCylinder_eq,
    tensorUnitPullbackSmallCoefficientCylinder_eq]

end AlgebraicGeometry.Scheme.Modules
