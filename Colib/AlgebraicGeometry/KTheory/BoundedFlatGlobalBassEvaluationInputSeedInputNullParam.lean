/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedCarrier
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterEnds
public import Colib.Topology.Path.CarrierSquareDescent

/-!
# Exact two-sheet parameters of the original input null square

The actual chart square is pasted to its original moving polynomial cylinder. Its boundary
collapse, original three-piece associator, and final quotient descent retain the selected
surface on each of the two distinct sheets.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputNull
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual Laurent inclusion on the ordinary or separately unit-shifted sheet. -/
def sheet (e : Bool) : C(|nerve (Codiscrete (Node (laurentRef g)))|, Carrier g) :=
  if e then
    (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g)).comp
        (mapParameter (ModelSimplex.reanchorNode (commonUnit g)))
  else CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)

/-- The unchanged polynomial cylinder on the specified separate sheet. -/
def cylinder (e : Bool) : C(|nerve (Codiscrete (Node (polyRef g)))| × I, Carrier g) :=
  if e then CutOpenCarrier.cylinderPlus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)
  else CutOpenCarrier.cylinderMinus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)

/-- The two terminal scalar points stay separate. -/
def tip (e : Bool) : Carrier g :=
  if e then CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)
  else CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)

/-- The original chart attachment agrees before realization on either sheet. -/
theorem cylinder_zero (e : Bool) (p : |nerve (Codiscrete (Node (polyRef g)))|) :
    cylinder g e (p, 0) = sheet g e
      (mapParameter (attachPostcompNode (polyRef g) (chart (X := X))
        (laurentRef g) (ordinary g)) p) := by
  cases e
  · exact CutOpenCarrier.cylinderMinus_zero _ _ _ _ _ p
  · change CutOpenCarrier.cylinderPlus _ _ _ _ _ (p, 0) = _
    rw [CutOpenCarrier.cylinderPlus_zero]
    exact congrArg (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X))
      (laurentRef g) (ordinary g) (shifted g))
      (reanchor_attach_parameter (polyRef g) (chart (X := X)) (laurentRef g)
        (commonUnit g) (ordinary g) p).symm

/-- Each original cylinder retains its own terminal tip. -/
theorem cylinder_one (e : Bool) (p : |nerve (Codiscrete (Node (polyRef g)))|) :
    cylinder g e (p, 1) = tip g e := by
  cases e
  · exact CutOpenCarrier.cylinderMinus_one _ _ _ _ _ p
  · exact CutOpenCarrier.cylinderPlus_one _ _ _ _ _ p

/-- Every original complete chart node, on its specified sheet. -/
def vertex (e : Bool) (i : Fin 8) : Carrier g :=
  sheet g e (CommonReferenceNerve.parameter (laurentRef g)
    (InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection) (StdSimplex.single i))

/-- The original complete-node chart edge with its unchanged affine clock. -/
def edge (e : Bool) (i j : Fin 8) : Path (vertex g e i) (vertex g e j) :=
  (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection i j).map
    (sheet g e).continuous

/-- The original polynomial evaluation edge, before the positive chart attachment. -/
def polynomialEdge :=
  (SimplexParameters.edge (k := 7) 0 3).map
    (CommonReferenceNerve.parameter (polyRef g)
      (InputSpanParameterNodes.projectionNodes g)).continuous

private def polyFace : ⦋1⦌ ⟶ ⦋7⦌ := SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩
private def chartFace : ⦋1⦌ ⟶ ⦋7⦌ := SimplexCategory.Hom.mk ⟨![6, 7], by decide⟩

/-- The whole moving cylinder seam is proved using both complete original reference nodes. -/
theorem polynomial_attach (r : I) :
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X))
      (laurentRef g) (ordinary g)) (polynomialEdge g r) =
        InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 6 7 r := by
  change mapParameter _ (CommonReferenceNerve.parameter _ _
    (SimplexParameters.edge (k := 7) 0 3 r)) = _
  rw [mapParameter_parameter]
  have h := parameter_eq_of_face_nodes (laurentRef g)
    (InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection)
    (InputSpanParameterNodes.nodes g plus GlobalRawBass.plus_projection)
    chartFace polyFace (fun i ↦ by
      fin_cases i
      · exact (InputSpanParameterEdges.projection_pre_source g plus
          GlobalRawBass.plus_projection).trans
          (InputChartFaceNodes.pre_target_node g plus GlobalRawBass.plus_projection).symm
      · exact InputSpanParameterEdges.projection_chart_target g plus
          GlobalRawBass.plus_projection) (SimplexParameters.edge (k := 1) 0 1 r)
  have hp : StdSimplex.map polyFace.toOrderHom (SimplexParameters.edge (k := 1) 0 1 r) =
      SimplexParameters.edge (k := 7) 0 3 r := SimplexParameters.map_edge polyFace 0 1 r
  have hc : StdSimplex.map chartFace.toOrderHom (SimplexParameters.edge (k := 1) 0 1 r) =
      SimplexParameters.edge (k := 7) 6 7 r := SimplexParameters.map_edge chartFace 0 1 r
  rw [hp, hc] at h
  exact h

/-- Both original chart times precede the actual sheet inclusion. -/
def chartParameter (e : Bool) : C(I × I, Carrier g) :=
  (sheet g e).comp (InputChartSquareParameter.plusParameter g)

/-- The unmodified split raw positive-chart word is retained inside the target null. -/
def rawPath (e : Bool) : Path (vertex g e 4) (vertex g e 7) :=
  (((edge g e 1 2).trans (edge g e 2 4)).symm).trans
    ((edge g e 1 5).trans (edge g e 5 7))

/-- The first original moving square, with path time exchanged only for literal pasting. -/
def chartSwap (e : Bool) : (edge g e 0 3).toContinuousMap.Homotopy
    (edge g e 6 7).toContinuousMap where
  toFun z := chartParameter g e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := congrArg (sheet g e)
    (InputChartSquareParameter.parameter_left g plus GlobalRawBass.plus_projection r)
  map_one_left r := congrArg (sheet g e)
    (InputChartSquareParameter.parameter_right g plus GlobalRawBass.plus_projection r)

/-- The second original half is the full cone cylinder moving along polynomial evaluation. -/
def cylinderSwap (e : Bool) : (edge g e 6 7).toContinuousMap.Homotopy
    (Path.refl (tip g e)).toContinuousMap where
  toFun z := cylinder g e (polynomialEdge g z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (cylinder_zero g e _).trans
    (congrArg (sheet g e) (polynomial_attach g r))
  map_one_left r := cylinder_one g e _

/-- The actual initial polynomial null, beginning at the complete sixth chart node. -/
def sourceCylinder (e : Bool) : Path (vertex g e 6) (tip g e) where
  toFun s := cylinder g e (polynomialEdge g 0, s)
  continuous_toFun := by fun_prop
  source' := ((cylinderSwap g e).apply_zero 0).trans (edge g e 6 7).source
  target' := cylinder_one g e _

/-- The actual final polynomial null, beginning at the complete seventh chart node. -/
def targetCylinder (e : Bool) : Path (vertex g e 7) (tip g e) where
  toFun s := cylinder g e (polynomialEdge g 1, s)
  continuous_toFun := by fun_prop
  source' := ((cylinderSwap g e).apply_zero 1).trans (edge g e 6 7).target
  target' := cylinder_one g e _

/-- The original direct null track, with its original half cut. -/
def sourcePath (e : Bool) := (edge g e 0 6).trans (sourceCylinder g e)

/-- The original composite null track, with its original half and quarter cuts. -/
def targetPath (e : Bool) :=
  (edge g e 3 4).trans ((rawPath g e).trans (targetCylinder g e))

/-- The original pasted-square null before its prescribed composition reassociation. -/
def pastedPath (e : Bool) :=
  ((edge g e 3 4).trans (rawPath g e)).trans (targetCylinder g e)

/-- The selected moving-null square retains its two original path-time halves. -/
def movingSquare (e : Bool) : Topology.CarrierPathSquare.Square
    (sourcePath g e) (pastedPath g e) (edge g e 0 3) (Path.refl (tip g e)) where
  parameter := ⟨fun z ↦ ((chartSwap g e).trans (cylinderSwap g e)) (z.2, z.1), by fun_prop⟩
  at_zero s := by
    change ((chartSwap g e).trans (cylinderSwap g e)) (s, 0) =
      ((edge g e 0 6).trans (sourceCylinder g e)) s
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact congrArg (sheet g e)
        (InputChartSquareParameter.parameter_zero g plus GlobalRawBass.plus_projection _)
    · rfl
  at_one s := by
    have h (t : I) : chartParameter g e (1, t) =
        ((edge g e 3 4).trans (rawPath g e)) t := by
      have h := congrArg (sheet g e)
        (InputChartSquareParameter.parameter_one g plus GlobalRawBass.plus_projection t)
      change chartParameter g e (1, t) =
        (((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 3 4).trans
          (((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 1 2).trans
            (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 2 4)).symm.trans
            ((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 1 5).trans
              (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 5 7)))).map
                (sheet g e).continuous) t at h
      simpa only [Path.map_trans, ← Path.map_symm, edge, rawPath] using h
    change ((chartSwap g e).trans (cylinderSwap g e)) (s, 1) =
      (((edge g e 3 4).trans (rawPath g e)).trans (targetCylinder g e)) s
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact h _
    · rfl
  left r := ((chartSwap g e).trans (cylinderSwap g e)).apply_zero r
  right r := ((chartSwap g e).trans (cylinderSwap g e)).apply_one r

/-- The original three-piece correction, without any alternative same-boundary filler. -/
def correction (e : Bool) : (pastedPath g e).Homotopy (targetPath g e) :=
  Path.Homotopy.transAssoc (edge g e 3 4) (rawPath g e) (targetCylinder g e)

/-- The complete original collapsed-boundary and correction word. -/
def boundaryComparison (e : Bool) : (sourcePath g e).Homotopy
    (((edge g e 0 3).trans (targetPath g e)).trans (Path.refl (tip g e)).symm) :=
  (movingSquare g e).toBoundary.trans
    ((((Path.Homotopy.refl (edge g e 0 3)).hcomp (correction g e))).hcomp
      (Path.Homotopy.refl (Path.refl (tip g e))).symm)

/-- Quotient descent retains the entire selected original null surface on the given sheet. -/
def square (e : Bool) : Topology.CarrierPathSquare.Square
    (sourcePath g e) (targetPath g e) (edge g e 0 3) (Path.refl (tip g e)) :=
  Topology.CarrierPathSquare.boundarySquare (boundaryComparison g e)

/-- The genuine compact carrier square for the whole original input null surface. -/
def parameter (e : Bool) : C(I × I, Carrier g) := (square g e).parameter

/-- The entire direct null edge has its original clock. -/
theorem parameter_zero (e : Bool) (s : I) : parameter g e (0, s) = sourcePath g e s :=
  (square g e).at_zero s

/-- The entire composite null edge has its original nested clocks. -/
theorem parameter_one (e : Bool) (s : I) : parameter g e (1, s) = targetPath g e s :=
  (square g e).at_one s

/-- The whole Laurent evaluation edge is the original unpaused chart edge. -/
theorem parameter_left (e : Bool) (r : I) : parameter g e (r, 0) = edge g e 0 3 r :=
  (square g e).left r

/-- The terminal edge remains the separate scalar tip for the specified sheet. -/
theorem parameter_right (e : Bool) (r : I) : parameter g e (r, 1) = tip g e :=
  (square g e).right r

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputNull
