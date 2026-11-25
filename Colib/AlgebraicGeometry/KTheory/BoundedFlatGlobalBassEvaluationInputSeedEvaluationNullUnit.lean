/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNullRails
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationUnitNerve
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveSeed
public import Colib.Topology.Path.Homotopy.RetypedUnitComparison

/-!
# Exact unit seams of the objectwise evaluation null sheets

The original four-node unit surface meets the ordinary and shifted Laurent evaluation rails
as complete nerve parameters. Endpoint retyping retains its two original triangular clocks.
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
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullUnit
open CommonReferenceNerve InputSeedEvaluationCarrier InputSeedEvaluationNullChart
attribute [local irreducible] GlobalSectionChangeIndex.evaluationUnitPasting

private theorem comparison_level_congr {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H K : Homotopy f g} (J J' : H.RelHomotopy K) (h : J = J')
    (n : ℕ) : (J.level n).toContinuousMap = (J'.level n).toContinuousMap :=
  congrArg (fun W => (W.level n).toContinuousMap) h

private theorem comp_value {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (F : C(A, C)) (G : C(B, C)) (q q' : C(A, B))
    (h : F = G.comp q) (hq : q = q') (a : A) : F a = G (q' a) := by
  rw [h, hq]
  rfl

variable (X : Scheme.{u})

/-- The four original complete unit nodes at the actual Laurent projection. -/
abbrev unitNodes := InputSeedEvaluationUnit.nodes (GlobalRawBass.laurentProjection.app X)
  (laurentScalar (op X))

/-- The original four-node unit simplex maps into the unchanged Laurent summand. -/
def unitMap : C(StdSimplex ℝ (Fin 4), Carrier X) :=
  (CutOpenCarrier.laurentInclusion (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)).comp (parameter (laurentRef X) (unitNodes X))

/-- The common chart's actual Laurent evaluation edge. -/
def chartFace : ⦋1⦌ ⟶ ⦋7⦌ := SimplexCategory.Hom.mk ⟨![0, 1], by decide⟩

/-- The lower full-reference edge of the original unit square. -/
def lowerFace : ⦋1⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 2], by decide⟩

/-- The separately unit-shifted full-reference edge. -/
def upperFace : ⦋1⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![1, 3], by decide⟩

/-- Both lower endpoints agree as full original dependent nodes. -/
theorem lower_nodes (i : Fin 2) :
    InputChartSimplex.nodes X (chartFace.toOrderHom i) =
      unitNodes X (lowerFace.toOrderHom i) := by
  fin_cases i
  · exact InputChartSimplex.chartNodes_zero X (plus.app X) (GlobalRawBass.plus_projection X)
  · exact InputChartSimplex.chartNodes_one X (plus.app X) (GlobalRawBass.plus_projection X)

/-- Both upper endpoints retain the actual original common-unit reference. -/
theorem upper_nodes (i : Fin 2) :
    ModelSimplex.reanchorNode (commonUnit X)
      (InputChartSimplex.nodes X (chartFace.toOrderHom i)) =
      unitNodes X (upperFace.toOrderHom i) := by
  rw [lower_nodes]
  fin_cases i
  · change (⟨_, commonUnit X ≪≫ Iso.refl _⟩ : Node (laurentRef X)) = ⟨_, commonUnit X⟩
    exact congrArg (fun a => (⟨laurentRef X, a⟩ : Node (laurentRef X))) (Iso.trans_refl _)
  · rfl

private theorem map_edge {k l : ℕ} (α : ⦋k⦌ ⟶ ⦋l⦌) (i j : Fin (k + 1)) (s : I) :
    StdSimplex.map α.toOrderHom (edge i j s) =
      edge (α.toOrderHom i) (α.toOrderHom j) s :=
  StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm s))
    (unitInterval.nonneg s) (by simp) i j α.toOrderHom

/-- The full lower original evaluation edge agrees in the actual Laurent nerve. -/
theorem lower_parameter (s : I) :
    parameter (laurentRef X) (InputChartSimplex.nodes X) (edge (k := 7) 0 1 s) =
      parameter (laurentRef X) (unitNodes X) (edge (k := 3) 0 2 s) := by
  have h := parameter_eq_of_face_nodes (laurentRef X) (unitNodes X)
    (InputChartSimplex.nodes X) lowerFace chartFace (lower_nodes X) (edge (k := 1) 0 1 s)
  have hc : StdSimplex.map chartFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 7) 0 1 s := map_edge chartFace 0 1 s
  have hl : StdSimplex.map lowerFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 3) 0 2 s := map_edge lowerFace 0 1 s
  rw [hc, hl] at h
  exact h

/-- The full upper edge agrees before evaluation, with its actual shifted reference. -/
theorem upper_parameter (s : I) :
    mapParameter (ModelSimplex.reanchorNode (commonUnit X))
      (parameter (laurentRef X) (InputChartSimplex.nodes X) (edge (k := 7) 0 1 s)) =
      parameter (laurentRef X) (unitNodes X) (edge (k := 3) 1 3 s) := by
  rw [mapParameter_parameter]
  have h := parameter_eq_of_face_nodes (laurentRef X) (unitNodes X)
    (fun i => ModelSimplex.reanchorNode (commonUnit X) (InputChartSimplex.nodes X i))
    upperFace chartFace (upper_nodes X) (edge (k := 1) 0 1 s)
  have hc : StdSimplex.map chartFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 7) 0 1 s := map_edge chartFace 0 1 s
  have hu : StdSimplex.map upperFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 3) 1 3 s := map_edge upperFace 0 1 s
  rw [hc, hu] at h
  exact h

/-- The original lower evaluation rail of the unit square. -/
abbrev lower := (edge (k := 3) 0 2).map (unitMap X).continuous
/-- Its separately unit-shifted upper evaluation rail. -/
abbrev upper := (edge (k := 3) 1 3).map (unitMap X).continuous
/-- The original forward strict unit edge. -/
abbrev oldUnitPath := (edge (k := 3) 0 1).map (unitMap X).continuous
/-- The original forward raw unit edge. -/
abbrev newUnitPath := (edge (k := 3) 2 3).map (unitMap X).continuous

/-- The entire original lower Laurent rail meets the ordinary null sheet. -/
theorem lower_rail (s : I) : lower X s = laurentMovement X false s :=
  congrArg (CutOpenCarrier.laurentInclusion (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)) (lower_parameter X s).symm

/-- The entire original upper Laurent rail meets the shifted null sheet. -/
theorem upper_rail (s : I) : upper X s = laurentMovement X true s :=
  congrArg (CutOpenCarrier.laurentInclusion (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)) (upper_parameter X s).symm

/-- The whole original two-triangle unit comparison in the carrier. -/
def unitSurface : ((oldUnitPath X).trans (upper X)).Homotopy
    ((lower X).trans (newUnitPath X)) :=
  (InputSeedEvaluationUnit.scalarParameter.map (unitMap X)).cast
    (by simp only [Path.map_trans]) (by simp only [Path.map_trans])

/-- The original old unit with the proved null-sheet source endpoints. -/
abbrev oldUnit := Path.RetypedUnitComparison.oldUnit (oldUnitPath X)
  (lower X) (upper X) (laurentMovement X false) (laurentMovement X true)
  (lower_rail X) (upper_rail X)

/-- The original new unit with the proved null-sheet target endpoints. -/
abbrev newUnit := Path.RetypedUnitComparison.newUnit (newUnitPath X)
  (lower X) (upper X) (laurentMovement X false) (laurentMovement X true)
  (lower_rail X) (upper_rail X)

/-- Endpoint retyping preserves the complete originally chosen unit surface. -/
def unitComparison : ((oldUnit X).trans (laurentMovement X true)).Homotopy
    ((laurentMovement X false).trans (newUnit X)) :=
  Path.RetypedUnitComparison.comparison (oldUnitPath X) (newUnitPath X)
    (lower X) (upper X) (laurentMovement X false) (laurentMovement X true)
    (lower_rail X) (upper_rail X) (unitSurface X)

/-- Endpoint retyping preserves each value of the originally selected carrier surface. -/
theorem unitComparison_apply (r s : I) :
    unitComparison X (r, s) = unitSurface X (r, s) :=
  Path.RetypedUnitComparison.comparison_apply (oldUnitPath X) (newUnitPath X)
    (lower X) (upper X) (laurentMovement X false) (laurentMovement X true)
    (lower_rail X) (upper_rail X) (unitSurface X) r s

/-- The original scalar parameter survives mapping and endpoint casting unchanged. -/
theorem unitSurface_apply (r s : I) :
    unitSurface X (r, s) = unitMap X (InputSeedEvaluationUnit.scalarParameter (r, s)) := rfl

/-- The unchanged Laurent carrier inclusion evaluates the original four-node parameter. -/
theorem unitSurface_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (unitSurface X (r, s)) x =
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
        ((GlobalSectionChangeIndex.evaluationUnitPasting (GlobalRawBass.laurentProjection.app X)
          (laurentScalar (op X))).level n (r, (s, x))) := by
  rw [unitSurface_apply]
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (InputSeedEvaluationUnit.parameter (GlobalRawBass.laurentProjection.app X)
        (laurentScalar (op X)) (r, s))) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion, InputSeedEvaluationUnit.parameter_native]
  rfl

private theorem laurentPasting_eq :
    GlobalSectionChangeIndex.globalLaurentEvaluationPasting (op X) =
      GlobalSectionChangeIndex.evaluationUnitPasting (GlobalRawBass.laurentProjection.app X)
        (laurentScalar (op X)) := rfl

/-- The original positive unit wrapper preserves the whole continuous family. -/
theorem unitPasting_level (n : ℕ) :
    ((InputPositive.unitPasting X).level n).toContinuousMap =
      ((mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n).comp
        ((GlobalSectionChangeIndex.globalLaurentEvaluationPasting (op X)).level n).toContinuousMap
    := rfl

/-- The original positive unit wrapper changes only its endpoint proofs. -/
theorem unitPasting_value (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    (InputPositive.unitPasting X).level n (r, (s, x)) =
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
        ((GlobalSectionChangeIndex.evaluationUnitPasting (GlobalRawBass.laurentProjection.app X)
          (laurentScalar (op X))).level n (r, (s, x))) :=
  comp_value ((InputPositive.unitPasting X).level n).toContinuousMap
    ((mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n)
    ((GlobalSectionChangeIndex.globalLaurentEvaluationPasting (op X)).level n).toContinuousMap
    ((GlobalSectionChangeIndex.evaluationUnitPasting (GlobalRawBass.laurentProjection.app X)
      (laurentScalar (op X))).level n).toContinuousMap
    (unitPasting_level X n) (comparison_level_congr _ _ (laurentPasting_eq X) n) (r, (s, x))

/-- Every original unit-pasting value is retained after the full-rail endpoint transport. -/
theorem unitComparison_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (unitComparison X (r, s)) x =
      (InputPositive.unitPasting X).level n (r, (s, x)) := by
  rw [unitComparison_apply]
  exact (unitSurface_native X n r s x).trans (unitPasting_value X n r s x).symm

/-- The entire original forward strict unit is recovered, including both endpoints. -/
theorem oldUnit_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (oldUnit X s) x =
      (InputPositive.oldUnit X).level n (s, x) := by
  let ev := fun z : Carrier X => CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X) n z x
  apply Path.Evaluation.left_factor ev (oldUnit X) (laurentMovement X true)
    ((InputPositive.oldUnit X).path n x) ((InputPositiveNull.laurentMovement X).path n x)
  intro t
  have h := unitComparison_native X n 0 t x
  change ev ((unitComparison X).toFun (0, t)) = _ at h
  rw [(unitComparison X).map_zero_left] at h
  exact h.trans (((InputPositive.unitPasting X).level n).apply_zero (t, x))

/-- The entire original forward raw unit is recovered at the unchanged unit clock. -/
theorem newUnit_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (newUnit X s) x =
      (InputPositive.newUnit X).level n (s, x) := by
  let ev := fun z : Carrier X => CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X) n z x
  apply Path.Evaluation.right_factor ev (laurentMovement X false) (newUnit X)
    ((InputPositiveNull.laurentMovement X).path n x) ((InputPositive.newUnit X).path n x)
  intro t
  have h := unitComparison_native X n 1 t x
  change ev ((unitComparison X).toFun (1, t)) = _ at h
  rw [(unitComparison X).map_one_left] at h
  exact h.trans (((InputPositive.unitPasting X).level n).apply_one (t, x))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullUnit
