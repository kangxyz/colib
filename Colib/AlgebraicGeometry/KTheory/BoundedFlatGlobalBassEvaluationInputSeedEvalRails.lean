/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalNullParam
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedCornerNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedProductRails

/-! Full Laurent rails join the two original moving nulls to the actual unit product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalRails
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private def lowerFace : ⦋1⦌ ⟶ ⦋15⦌ := SimplexCategory.Hom.mk ⟨![6, 7], by decide⟩
private def upperFace : ⦋1⦌ ⟶ ⦋15⦌ := SimplexCategory.Hom.mk ⟨![14, 15], by decide⟩

/-- The whole binary source is the actual second original evaluation rail. -/
theorem binary_source (r : I) : InputSeedEvalBinary.parameter g (r, 0) =
    CommonReferenceNerve.parameter (laurentRef g) (InputSeedUnitNodes.nodes g)
      ((edge (k := 15) 6 7) r) := by
  change CommonReferenceNerve.parameter (laurentRef g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    (Topology.SimplexGrid.parameter.{u+1} 1 2
      ((edge (k := 1) 0 1) r, binaryPath (k := 2) 0 1 2 0)) = _
  rw [Path.source, Topology.SimplexGrid.parameter_column]
  have h := parameter_eq_of_face_nodes (laurentRef g) (InputSeedUnitNodes.nodes g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    lowerFace (Topology.SimplexGrid.columnFace 1 2 0)
    (fun i ↦ by
      fin_cases i
      · exact (InputSeedCornerNodes.pre_prism g).symm
      · exact (InputSeedCornerNodes.target_prism g).symm)
    ((edge (k := 1) 0 1) r)
  have he : StdSimplex.map lowerFace.toOrderHom ((edge (k := 1) 0 1) r) =
      (edge (k := 15) 6 7) r := map_edge lowerFace 0 1 r
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (laurentRef g) (InputSeedUnitNodes.nodes g)) he)

/-- The whole shifted rail keeps the same Model arrows and the actual common unit. -/
theorem shifted_rail (r : I) :
    mapParameter (ModelSimplex.reanchorNode (commonUnit g))
      (CommonReferenceNerve.parameter (laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 6 7) r)) =
    CommonReferenceNerve.parameter (laurentRef g) (InputSeedUnitNodes.nodes g)
      ((edge (k := 15) 14 15) r) := by
  rw [mapParameter_parameter]
  have h := parameter_eq_of_face_nodes (laurentRef g) (InputSeedUnitNodes.nodes g)
    (fun i ↦ ModelSimplex.reanchorNode (commonUnit g) (InputSeedUnitNodes.nodes g i))
    upperFace lowerFace (fun i ↦ by fin_cases i <;> rfl) ((edge (k := 1) 0 1) r)
  have hl : StdSimplex.map lowerFace.toOrderHom ((edge (k := 1) 0 1) r) =
      (edge (k := 15) 6 7) r := map_edge lowerFace 0 1 r
  have hu : StdSimplex.map upperFace.toOrderHom ((edge (k := 1) 0 1) r) =
      (edge (k := 15) 14 15) r := map_edge upperFace 0 1 r
  rw [hl, hu] at h
  exact h

/-- The middle moving unit is the unchanged product in the original Laurent inclusion. -/
def unit : C(I × I, Carrier g) :=
  (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)).comp (InputSeedEvaluationProduct.parameter g)

/-- The entire lower unit rail agrees with the entire ordinary null source. -/
theorem unit_zero (r : I) : unit g (r, 0) = InputSeedEvalNull.source g false r := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (InputSeedEvaluationProduct.parameter g (r, 0)) =
      CutOpenCarrier.laurentInclusion _ _ _ _ _ (InputSeedEvalBinary.parameter g (r, 0))
  rw [InputSeedProductRails.bottom, binary_source]

/-- The entire upper unit rail agrees with the entire shifted null source. -/
theorem unit_one (r : I) : unit g (r, 1) = InputSeedEvalNull.source g true r := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (InputSeedEvaluationProduct.parameter g (r, 1)) =
      CutOpenCarrier.laurentInclusion _ _ _ _ _
        (mapParameter (ModelSimplex.reanchorNode (commonUnit g))
          (InputSeedEvalBinary.parameter g (r, 0)))
  rw [InputSeedProductRails.top, binary_source, shifted_rail]

/-- At every evaluation input the original unit joins precisely the two null source points. -/
def unitPath (r : I) :
    Path (InputSeedEvalNull.source g false r) (InputSeedEvalNull.source g true r) where
  toFun s := unit g (r, s)
  continuous_toFun := by fun_prop
  source' := unit_zero g r
  target' := unit_one g r

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalRails
