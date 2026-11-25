/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalBinary

/-! Both complete original binary words on the two evaluation ends, before native evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalBinary
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The initial evaluation face is the entire original strict-precomposed raw binary word. -/
theorem source_parameter (s : I) : parameter g (0, s) =
    CommonReferenceNerve.parameter (laurentRef g)
      (InputChartReference.preNode g plus GlobalRawBass.plus_projection)
      (StdSimplex.map
        (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom
          (binaryPath (k := 2) 0 1 2 s)) := by
  change CommonReferenceNerve.parameter (laurentRef g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    (Topology.SimplexGrid.parameter.{u+1} 1 2
      ((edge (k := 1) 0 1) 0, binaryPath (k := 2) 0 1 2 s)) = _
  rw [Path.source, Topology.SimplexGrid.parameter_row]
  exact parameter_eq_of_face_nodes (laurentRef g)
    (InputChartReference.preNode g plus GlobalRawBass.plus_projection)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    (InputSimplex.triangleFace 1 2 4 (by decide) (by decide))
    (Topology.SimplexGrid.rowFace 1 2 0)
    (InputChartReference.prism_pre_nodes g plus GlobalRawBass.plus_projection) _

/-- The final evaluation face is the entire original converted raw binary word. -/
theorem target_parameter (s : I) : parameter g (1, s) =
    CommonReferenceNerve.parameter (laurentRef g)
      (InputChartReference.rawNode g plus GlobalRawBass.plus_projection)
      (StdSimplex.map InputRectangleNodes.preNormalizationFace.toOrderHom
        (binaryPath (k := 2) 0 1 2 s)) := by
  change CommonReferenceNerve.parameter (laurentRef g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    (Topology.SimplexGrid.parameter.{u+1} 1 2
      ((edge (k := 1) 0 1) 1, binaryPath (k := 2) 0 1 2 s)) = _
  rw [Path.target, Topology.SimplexGrid.parameter_row]
  exact parameter_eq_of_face_nodes (laurentRef g)
    (InputChartReference.rawNode g plus GlobalRawBass.plus_projection)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    InputRectangleNodes.preNormalizationFace (Topology.SimplexGrid.rowFace 1 2 1)
    (InputChartReference.prism_raw_nodes g plus GlobalRawBass.plus_projection) _

/-- The initial polynomial cylinder is based at precisely the sixth projection node. -/
theorem polynomial_source : polynomialParameter g 0 =
    CommonReferenceNerve.parameter (polyRef g) (InputSpanParameterNodes.projectionNodes g)
      (StdSimplex.single 6) := by
  change CommonReferenceNerve.parameter (polyRef g) _ ((edge (k := 7) 6 7) 0) = _
  rw [Path.source]

/-- The terminal polynomial cylinder is based at precisely the seventh projection node. -/
theorem polynomial_target : polynomialParameter g 1 =
    CommonReferenceNerve.parameter (polyRef g) (InputSpanParameterNodes.projectionNodes g)
      (StdSimplex.single 7) := by
  change CommonReferenceNerve.parameter (polyRef g) _ ((edge (k := 7) 6 7) 1) = _
  rw [Path.target]

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalBinary
