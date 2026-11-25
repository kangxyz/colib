/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityBoundaryNodes
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceReanchorAttachment

/-!
# Actual identity faces on both Laurent sheets of the fixed seed carrier

The fixed positive chart square, Laurent identity after the original positive normalization,
and original positive normalization after the source identity use their original full-node
families. Only their common reference is moved back to the original raw input reference.
Both independent times and the separate unit-shifted sheet are retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology Topology.LoopPrespectrum AlgebraicGeometry.RingedSpace SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedLaurentFaces
open CommonReferenceNerve ModelSimplex InputIdentitySeedCarrier
variable (X : Scheme.{u})

/-- Return the entire identity nerve to the unchanged original raw input reference. -/
def back : C(InputIdentityCarrierCharts.Carrier X,
    |nerve (Codiscrete (Node (laurentRef (𝟙 X))))|) :=
  mapParameter (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)

/-- The two actual sheets keep their separate original unit reference. -/
def sheet (e : Bool) : C(InputIdentityCarrierCharts.Carrier X, Carrier (𝟙 X)) :=
  (CutOpenCarrier.laurentInclusion (polyRef (𝟙 X)) (chart (X := X))
    (laurentRef (𝟙 X)) (ordinary (𝟙 X)) (shifted (𝟙 X))).comp
      ((if e then mapParameter (reanchorNode (commonUnit (𝟙 X))) else ContinuousMap.id _).comp
        (back X))

/-- The reference transport changes no native value of the whole identity nerve. -/
theorem sheet_native (e : Bool) (n : ℕ) (z : InputIdentityCarrierCharts.Carrier X)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (sheet X e z) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      (pointwisePrespectrumFamily (InputIdentityNodes.source X) n z x) := by
  cases e
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (mapParameter _ z)) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion]
    exact congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
      (pointwise_reanchor (InputIdentityNodes.inputSourceIso X).symm n z x)
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (mapParameter _ (mapParameter _ z))) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion]
    exact congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
      ((pointwise_reanchor (commonUnit (𝟙 X)) n _ x).trans
        (pointwise_reanchor (InputIdentityNodes.inputSourceIso X).symm n z x))

/-- The original geometric plus identity square, on either full-reference sheet. -/
def chartFace (e : Bool) : C(I × I, Carrier (𝟙 X)) :=
  (sheet X e).comp (InputIdentityCarrierCharts.chartFace X plus plus_projection)

/-- Every chart-square point is the fixed actual identity square at the original projection. -/
theorem chartFace_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (chartFace X e (r, s)) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((InputIdentity.plusSquare X).level n
        (r, (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x))) := by
  exact (sheet_native X e n _ x).trans
    (congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
      ((pointwisePrespectrumFamily_eq_compact _ _ n (r, s) x).trans
        (InputIdentityCarrierCharts.plusFace_native X n r s x)))

/-- The original positive binary time is independent of Laurent identity time. -/
def targetParameter : C(I × I, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 2
    (binaryPath (k := 4) 0 1 2 z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The complete original positive normalization followed by the Laurent identity. -/
def targetPositive (e : Bool) : C(I × I, Carrier (𝟙 X)) :=
  (sheet X e).comp ((parameter (InputIdentityNodes.source X)
    (InputIdentityCarrierBottom.nodes X)).comp (targetParameter.{u}))

/-- The target face keeps the genuine Laurent map-id homotopy and its independent time. -/
theorem targetPositive_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (targetPositive X e (r, s)) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((InputIdentity.laurentHomotopy X).level n
        (r, (plusHomotopy X).level n (s, x))) := by
  refine (sheet_native X e n _ x).trans ?_
  apply congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
  change pointwisePrespectrumFamily _ n (parameter _ _ (targetParameter.{u} (r, s))) x = _
  rw [pointwisePrespectrumFamily_parameter]
  change prespectrumSimplexFamily (InputIdentityCarrierBottom.simplex X) n
    (targetParameter.{u} (r, s), x) = _
  rw [InputIdentityCarrierBottom.product_family]
  refine (CommonReferenceProduct.prespectrum_comp
    (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
    (fun i ↦ (InputIdentityProjection.nodes X i).2)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
      (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X))
    (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X)) n x
    (binaryPath (k := 4) 0 1 2 s) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  exact (InputIdentityCarrierBottom.laurent_native X n r _).trans
    (congrArg (fun y ↦ (InputIdentity.laurentHomotopy X).level n (r, y))
      (InputIdentityProjection.plus_native X n s x))

/-- Source identity time and the original positive binary time are separate coordinates. -/
def sourceParameter : C(I × I, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 z.1, binaryPath (k := 4) 0 1 2 z.2), by fun_prop⟩

/-- The original positive normalization applied after the unchanged source identity. -/
def sourcePositive (e : Bool) : C(I × I, Carrier (𝟙 X)) :=
  (sheet X e).comp ((parameter (InputIdentityNodes.source X)
    (InputIdentityTopNodes.middleNodes X)).comp (sourceParameter.{u}))

/-- The whole source face retains the original split source identity, including level zero. -/
theorem sourcePositive_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (sourcePositive X e (r, s)) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((plusHomotopy X).level n
        (s, (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x))) := by
  refine (sheet_native X e n _ x).trans ?_
  apply congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
  change pointwisePrespectrumFamily _ n (parameter _ _ (sourceParameter.{u} (r, s))) x = _
  rw [pointwisePrespectrumFamily_parameter]
  refine (CommonReferenceProduct.prespectrum_comp
    (BoundedFlatPerfectIdentitySimplex.source X)
    (BoundedFlatPerfectIdentitySimplex.identityVertices X)
    (BoundedFlatPerfectIdentitySimplex.identityReferences X)
    (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
    (fun i ↦ (InputIdentityProjection.nodes X i).2) n x
    (binaryPath (k := 2) 0 1 2 r) (binaryPath (k := 4) 0 1 2 s)).trans ?_
  refine (congrArg (fun y ↦ prespectrumSimplexFamily (InputIdentityProjection.simplex X)
    n (binaryPath (k := 4) 0 1 2 s, y)) (BoundedFlatPerfectIdentitySimplex.identity_native X n r
      x)).trans ?_
  exact InputIdentityProjection.plus_native X n s _

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedLaurentFaces
