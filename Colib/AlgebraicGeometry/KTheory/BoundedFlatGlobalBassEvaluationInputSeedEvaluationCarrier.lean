/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNormalizationPrismNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationStrictSeed
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenCompactFamily
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceReanchorAttachment

/-!
# The actual objectwise two-tip evaluation carrier

The polynomial evaluation edge attaches to the original positive chart's full cut nodes.
The second sheet retains the strict forward Laurent unit before that same ordinary anchor.
Both cone tips remain distinct, and all original geometric chart parameters are available.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity CategoryTheory.Waldhausen Topology
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationCarrier
open GlobalSectionChangeIndex CommonReferenceNerve
variable (X : Scheme.{u})

/-- Original strict polynomial pullback followed by polynomial evaluation. -/
abbrev polyRef := boundedAboveFlatGlobalSectionModelFunctor.map (projection.app X).op ≫
  evaluationModel (op (polynomial.obj X))

/-- The actual normalized positive raw chart. -/
abbrev chart := evaluationRawMap (plus.app X)

/-- The original strict Laurent pullback followed by Laurent evaluation. -/
abbrev laurentRef := InputChartSimplex.sourceMap X

/-- The two full polynomial evaluation nodes, with the original comparison anchor. -/
def polynomialNodes : Fin 2 → Node (polyRef X) := fun i =>
  ⟨InputNormalizationPrism.firstVertices (projection.app X) i,
    InputNormalizationPrism.firstAnchors (projection.app X) i⟩


/-- The source polynomial node retains the full identity reference. -/
theorem polynomialNodes_zero : polynomialNodes X 0 = ⟨polyRef X, Iso.refl _⟩ := rfl

/-- The target polynomial node retains the original evaluation reference itself. -/
theorem polynomialNodes_one : polynomialNodes X 1 =
    ⟨evaluationModel (op X) ≫ evaluationRawMap (projection.app X),
      evaluationComparisonIso (projection.app X)⟩ := rfl

/-- The ordinary anchor is the complete original positive cut reference. -/
def ordinary : (laurentRef X).hom.toFunctor ≅ (polyRef X ≫ chart X).hom.toFunctor :=
  (InputChartSimplex.chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 3).2

/-- The actual strict forward Laurent unit, postwhiskered by original evaluation. -/
def commonUnit : (laurentRef X).hom.toFunctor ≅ (laurentRef X).hom.toFunctor :=
  isoWhiskerRight
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map
      (GlobalRawBass.laurentProjection.app X).op).hom.toFunctor
      (strictLaurentUnit (op X)))
    (evaluationModel (op (laurent.obj X))).hom.toFunctor


/-- Original evaluation transports the actual strict unit to its unchanged target action. -/
theorem commonUnit_eq_target : commonUnit X =
    onFunctor (laurentRef X).hom.toFunctor
      (evaluationSmallUnit (op (laurent.obj X))
        (laurentScalar (op X))) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact evaluationModel_unit (op (laurent.obj X))
    (laurentScalar (op X))
    ((boundedAboveFlatGlobalSectionModelFunctor.map
      (GlobalRawBass.laurentProjection.app X).op).hom.toFunctor.obj A)

/-- The second attachment retains the original unit before the complete ordinary anchor. -/
def shifted : (laurentRef X).hom.toFunctor ≅ (polyRef X ≫ chart X).hom.toFunctor :=
  commonUnit X ≪≫ ordinary X

/-- The two actual polynomial cylinders share their Laurent nerve but keep separate tips. -/
abbrev Carrier := CutOpenCarrier.space (polyRef X) (chart X) (laurentRef X)
  (ordinary X) (shifted X)

/-- The complete original polynomial comparison edge, before positive chart attachment. -/
def movement : C(I, |nerve (Codiscrete (Node (polyRef X)))|) :=
  (parameter (polyRef X) (polynomialNodes X)).comp (edge (k := 1) 0 1).toContinuousMap

/-- Every polynomial movement value is the unchanged evaluation comparison. -/
theorem movement_native (n : ℕ) (t : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    pointwisePrespectrumFamily (polyRef X) n (movement X t) x =
      (evaluationComparison (projection.app X)).level n (t, x) := by
  change pointwisePrespectrumFamily (polyRef X) n
    (parameter _ _ (edge (k := 1) 0 1 t)) x = _
  rw [pointwisePrespectrumFamily_parameter]
  exact InputNormalizationPrism.first_native (projection.app X) n t x

/-- The ordered polynomial edge in the original common chart simplex. -/
def polynomialFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩

private theorem attach_identity_reference
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} (J : B ⥤ C) {G : A ⥤ C} (e : G ≅ F ⋙ J) :
    e = e ≪≫ isoWhiskerRight (Iso.refl F) J := by
  rw [isoWhiskerRight_refl, Iso.trans_refl]

set_option maxHeartbeats 1200000 in
-- Matching the two dependent nodes reduces the concrete section and evaluation composites.
/-- Both attached nodes keep their entire original Model arrows and reference isomorphisms. -/
theorem polynomial_nodes (i : Fin 2) :
    InputChartSimplex.nodes X (polynomialFace.toOrderHom i) =
      attachPostcompNode (polyRef X) (chart X) (laurentRef X) (ordinary X)
        (polynomialNodes X i) := by
  fin_cases i
  · apply Sigma.ext
    · rfl
    apply heq_of_eq
    exact attach_identity_reference (chart X).hom.toFunctor (ordinary X)
  · apply Sigma.ext
    · rfl
    apply heq_of_eq
    have hh : InputSimplex.anchors (plus.app X) (projection.app X) 3 ≪≫
        evaluationCompositionSecondIso (plus.app X) (projection.app X) =
        InputSimplex.anchors (plus.app X) (projection.app X) 4 :=
      Iso.ext (evaluationComposition_pasting (plus.app X) (projection.app X)).symm
    change eqToIso _ ≪≫ InputSimplex.anchors (plus.app X) (projection.app X) 4 =
      (eqToIso _ ≪≫ InputSimplex.anchors (plus.app X) (projection.app X) 3) ≪≫
        evaluationCompositionSecondIso (plus.app X) (projection.app X)
    rw [Iso.trans_assoc, hh]

/-- The entire polynomial edge attaches before evaluation, including its original clock. -/
theorem movement_attach (t : I) :
    parameter (laurentRef X) (InputChartSimplex.nodes X) (edge (k := 7) 3 4 t) =
      mapParameter (attachPostcompNode (polyRef X) (chart X) (laurentRef X) (ordinary X))
        (movement X t) := by
  change parameter _ _ _ = mapParameter _ (parameter _ _ (edge (k := 1) 0 1 t))
  rw [mapParameter_parameter]
  have h := parameter_face (laurentRef X) (InputChartSimplex.nodes X)
    polynomialFace (edge (k := 1) 0 1 t)
  have he : StdSimplex.map polynomialFace.toOrderHom (edge (k := 1) 0 1 t) =
      edge (k := 7) 3 4 t :=
    StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
      (unitInterval.nonneg t) (by simp) 0 1 polynomialFace.toOrderHom
  rw [he] at h
  exact h.trans (congrArg (fun nodes => parameter (laurentRef X) nodes (edge (k := 1) 0 1 t))
    (funext (polynomial_nodes X)))

/-- The same entire edge attaches to the separately unit-shifted cone sheet. -/
theorem shifted_movement_attach (t : I) :
    mapParameter (ModelSimplex.reanchorNode (commonUnit X))
      (parameter (laurentRef X) (InputChartSimplex.nodes X) (edge (k := 7) 3 4 t)) =
      mapParameter (attachPostcompNode (polyRef X) (chart X) (laurentRef X) (shifted X))
        (movement X t) := by
  rw [movement_attach]
  exact reanchor_attach_parameter (polyRef X) (chart X) (laurentRef X)
    (commonUnit X) (ordinary X) (movement X t)

/-- The two genuine tips remain distinct before native evaluation. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef X) (chart X) (laurentRef X) (ordinary X) (shifted X) ≠
      CutOpenCarrier.tipPlus (polyRef X) (chart X) (laurentRef X) (ordinary X) (shifted X) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationCarrier
