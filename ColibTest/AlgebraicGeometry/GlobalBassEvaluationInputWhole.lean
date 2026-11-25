/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNaturality

/-! Regression checks for the actual complete one-step mixed input cube and cone law. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace ColibTest.GlobalBassEvaluationInputWhole
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The source and target sheets meet on their entire original nerve edge. -/
theorem full_pasted_seam (s : unitInterval) :
    InputMixedDesc.postSquareParameter g (1, s) = InputRawPastedParameter.parameter g (0, s) :=
  InputRawPastedSeam.seam g s

/-- Every native level of the entire target face is the literal original pasted track. -/
theorem target_whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputTargetFace.parameter g) n = InputTargetFace.nativeFamily g n :=
  InputTargetFace.whole_native g n

/-- The completed cube keeps both of the entire prescribed original comparison faces. -/
theorem both_comparison_faces (r s : unitInterval) :
    InputCubeFaces.parameter g ![0, r, s] = InputMixedDesc.preSquareParameter g (r, s) ∧
      InputCubeFaces.parameter g ![1, r, s] = InputTargetFace.parameter g (r, s) :=
  ⟨InputCubeFaces.zero g r s, InputCubeFaces.one g r s⟩

/-- The original overlap keeps all three cube times, including genuine degree-zero inputs. -/
theorem cube_zero_input (q r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space 0) :
    (InputCube.cylinder g).level 0 (q, (r, (s, x))) =
      CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
        (InputCubeFaces.parameter g) 0 (![q, r, s], x) := rfl

/-- The original strict cone input adds no extra half to the source evaluation cone. -/
theorem literal_strict_cone :
    InputConeSource.strictConeMap g ≫ coneEvaluation X = InputConeSource.directConeMap g :=
  InputConeSource.strict_comp_evaluation g

/-- The actual strict Bass input and independent raw input are compared by a whole homotopy. -/
theorem actual_step_input : Nonempty (Homotopy
    ((((KTheory.Bass.strictDiagramFunctor squareFunctor).obj
      sectionDiagram).map g.op) ≫ stepEvaluation X)
    (stepEvaluation Y ≫ GlobalRawBass.map g)) :=
  ⟨InputNaturality.stepHomotopy g⟩

/-- The actual cone homotopy retains the unpaused Laurent comparison at every point. -/
theorem actual_laurent_face (n : ℕ) (r : unitInterval)
    (x : (sectionDiagram.obj (op (laurent.obj Y))).space n) :
    (InputNaturality.coneHomotopy g).level n
      (r, (mappingConeInclusion (StrictSquare.comparison (sectionSquare Y))).map n x) =
      (mappingConeInclusion (GlobalRawBass.comparison X)).map n
        ((evaluationComparison (laurent.map g)).level n (r, x)) :=
  InputNaturality.coneHomotopy_inclusion g n r x

/-- Structure time stays independent of all three original overlap coordinates. -/
theorem independent_structure (n : ℕ) (q r s t : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (InputCube.cylinder g).level (n + 1)
      (q, (r, (s, (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).structureMap n x t))) =
      (prespectrum (asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace))).structureMap n
        ((InputCube.cylinder g).level n (q, (r, (s, x)))) t :=
  (InputCube.cylinder g).comm n q r s x t

/-- The actual null square uses the original cone cylinder at its unchanged height. -/
theorem actual_null_surface (n : ℕ) (q s : unitInterval)
    (x : (StrictSquare.span (sectionSquare Y)).space n) :
    (InputNaturality.originalNullSquare g).level n (q, (s, x)) =
      (InputNaturality.coneHomotopy g).level n
        (q, (mappingConeHomotopy (StrictSquare.comparison (sectionSquare Y))).level n (s, x)) :=
  InputNaturality.originalNullSquare_level g n q s x

end ColibTest.GlobalBassEvaluationInputWhole
