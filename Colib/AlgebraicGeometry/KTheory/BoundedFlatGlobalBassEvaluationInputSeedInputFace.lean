/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputRails
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveFactor
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedWords
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveSeed

/-!
# The entire original input-first seed face

The fixed whole input cone homotopy acts on the original strict seed. Its two exact original
null squares and strict-unit evaluation product are pasted as inverse-null / (unit / null),
retaining every original half and quarter clock and the two separate carrier tips.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u v w z
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputFace
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem trans_value {A : Type v} {B : Type w} {T : Type z}
    [TopologicalSpace A] [TopologicalSpace B] {p q k : C(A, B)}
    (P : p.Homotopy q) (Q : q.Homotopy k)
    {E F : LoopPrespectrum.{u}} {f h j : E ⟶ F}
    (H : Homotopy f h) (K : Homotopy h j) (n : ℕ) (x : E.space n)
    (ev : B → T) (out : F.space n → T) (a : A)
    (hP : ∀ t, ev (P (t, a)) = out (H.level n (t, x)))
    (hQ : ∀ t, ev (Q (t, a)) = out (K.level n (t, x))) (s : I) :
    ev ((P.trans Q) (s, a)) = out ((H.trans K).level n (s, x)) := by
  change ev ((P.trans Q) (s, a)) =
    out (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hP _
  · exact hQ _

/-- The original middle unit surface is included in the Laurent summand. -/
def unitParameter : C(I × I, Carrier g) :=
  (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)).comp (InputSeedInputUnitProduct.parameter g)

/-- The full ordinary middle rail is exactly the original lower null-square rail. -/
theorem unit_zero (r : I) : unitParameter g (r, 0) =
    InputSeedInputNull.edge g false 0 3 r :=
  congrArg (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)) (InputSeedInputRails.bottom_chart g r)

/-- The full shifted middle rail retains its original complete unit reference. -/
theorem unit_one (r : I) : unitParameter g (r, 1) =
    InputSeedInputNull.edge g true 0 3 r :=
  congrArg (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)) (InputSeedInputRails.top_chart g r)

/-- Exchange scalar coordinates only to paste along the original seed-path time. -/
def nullSwap (e : Bool) :
    (InputSeedInputNull.edge g e 0 3).toContinuousMap.Homotopy
      (ContinuousMap.const I (InputSeedInputNull.tip g e)) where
  toFun z := InputSeedInputNull.parameter g e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := InputSeedInputNull.parameter_left g e r
  map_one_left r := InputSeedInputNull.parameter_right g e r

/-- The original strict-unit action occupies precisely the middle seed-path segment. -/
def unitSwap : (InputSeedInputNull.edge g false 0 3).toContinuousMap.Homotopy
    (InputSeedInputNull.edge g true 0 3).toContinuousMap where
  toFun z := unitParameter g (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := unit_zero g r
  map_one_left r := unit_one g r

/-- The whole original seed word is pasted in its unchanged inverse-null/unit/null order. -/
def wordSwap : (ContinuousMap.const I (InputSeedInputNull.tip g false)).Homotopy
    (ContinuousMap.const I (InputSeedInputNull.tip g true)) :=
  (nullSwap g false).symm.trans ((unitSwap g).trans (nullSwap g true))

/-- Comparison time first and original seed time second, jointly continuously. -/
def parameter : C(I × I, Carrier g) :=
  ⟨fun z ↦ wordSwap g (z.2, z.1), by fun_prop⟩

/-- At each comparison time the null remains the selected original surface slice. -/
def nullPath (e : Bool) (r : I) :
    Path (InputSeedInputNull.edge g e 0 3 r) (InputSeedInputNull.tip g e) where
  toFun s := InputSeedInputNull.parameter g e (r, s)
  continuous_toFun := by fun_prop
  source' := InputSeedInputNull.parameter_left g e r
  target' := InputSeedInputNull.parameter_right g e r

/-- The whole initial null slice is the original source path with its unchanged clock. -/
theorem nullPath_zero (e : Bool) (s : I) :
    nullPath g e 0 s = InputSeedInputNull.sourcePath g e s :=
  InputSeedInputNull.parameter_zero g e s

/-- The whole terminal null slice retains the original nested target-null clock. -/
theorem nullPath_one (e : Bool) (s : I) :
    nullPath g e 1 s = InputSeedInputNull.targetPath g e s :=
  InputSeedInputNull.parameter_one g e s

/-- The moving middle path retains the exact original strict-unit product. -/
def unitPath (r : I) :
    Path (InputSeedInputNull.edge g false 0 3 r) (InputSeedInputNull.edge g true 0 3 r) where
  toFun s := unitParameter g (r, s)
  continuous_toFun := by fun_prop
  source' := unit_zero g r
  target' := unit_one g r

/-- The literal original path word at a fixed comparison time. -/
def path (r : I) : Path (InputSeedInputNull.tip g false) (InputSeedInputNull.tip g true) :=
  (nullPath g false r).symm.trans ((unitPath g r).trans (nullPath g true r))

/-- The jointly continuous parameter has the exact originally selected nested path clocks. -/
theorem parameter_apply (r s : I) : parameter g (r, s) = path g r s := rfl

/-- The original source unit, with its endpoints at the actual source chart nodes. -/
def sourceUnit : Path (InputSeedInputNull.vertex g false 0)
    (InputSeedInputNull.vertex g true 0) where
  toFun s := unitParameter g (0, s)
  continuous_toFun := by fun_prop
  source' := (unit_zero g 0).trans (InputSeedInputNull.edge g false 0 3).source
  target' := (unit_one g 0).trans (InputSeedInputNull.edge g true 0 3).source

/-- The original target unit, with both complete terminal chart references. -/
def targetUnit : Path (InputSeedInputNull.vertex g false 3)
    (InputSeedInputNull.vertex g true 3) where
  toFun s := unitParameter g (1, s)
  continuous_toFun := by fun_prop
  source' := (unit_zero g 1).trans (InputSeedInputNull.edge g false 0 3).target
  target' := (unit_one g 1).trans (InputSeedInputNull.edge g true 0 3).target

/-- The entire initial unit is the actual main-sixteen edge from lower0 to shifted0. -/
theorem sourceUnit_apply (s : I) : sourceUnit g s =
    CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g)
      (CommonReferenceNerve.parameter (laurentRef g) (InputSeedUnitNodes.nodes g)
        (CategoryTheory.Waldhausen.IteratedS.SimplexParameters.edge (k := 15) 0 8 s)) :=
  congrArg (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)) (InputSeedInputRails.source g s)

/-- The entire terminal unit is the actual main-sixteen edge from lower3 to shifted3. -/
theorem targetUnit_apply (s : I) : targetUnit g s =
    CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g)
      (CommonReferenceNerve.parameter (laurentRef g) (InputSeedUnitNodes.nodes g)
        (CategoryTheory.Waldhausen.IteratedS.SimplexParameters.edge (k := 15) 3 11 s)) :=
  congrArg (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)) (InputSeedInputRails.target g s)

/-- The complete initial inverse-null/unit/null word uses the original source null paths. -/
def sourceWord := (InputSeedInputNull.sourcePath g false).symm.trans
  ((sourceUnit g).trans (InputSeedInputNull.sourcePath g true))

/-- The complete terminal word retains the original nested target-null clocks. -/
def targetWord := (InputSeedInputNull.targetPath g false).symm.trans
  ((targetUnit g).trans (InputSeedInputNull.targetPath g true))

/-- The whole A edge equals its original source word before any native evaluation. -/
theorem source (s : I) : parameter g (0, s) = sourceWord g s := by
  rw [parameter_apply]
  exact Path.Evaluation.path_trans id (nullPath g false 0).symm
    ((unitPath g 0).trans (nullPath g true 0))
    (InputSeedInputNull.sourcePath g false).symm
    ((sourceUnit g).trans (InputSeedInputNull.sourcePath g true))
    (Path.Evaluation.path_symm id (nullPath g false 0)
      (InputSeedInputNull.sourcePath g false) (nullPath_zero g false))
    (Path.Evaluation.path_trans id (unitPath g 0) (nullPath g true 0)
      (sourceUnit g) (InputSeedInputNull.sourcePath g true) (fun _ ↦ rfl)
      (nullPath_zero g true)) s

/-- The whole B edge equals its original target word, with every nested cone height. -/
theorem target (s : I) : parameter g (1, s) = targetWord g s := by
  rw [parameter_apply]
  exact Path.Evaluation.path_trans id (nullPath g false 1).symm
    ((unitPath g 1).trans (nullPath g true 1))
    (InputSeedInputNull.targetPath g false).symm
    ((targetUnit g).trans (InputSeedInputNull.targetPath g true))
    (Path.Evaluation.path_symm id (nullPath g false 1)
      (InputSeedInputNull.targetPath g false) (nullPath_one g false))
    (Path.Evaluation.path_trans id (unitPath g 1) (nullPath g true 1)
      (targetUnit g) (InputSeedInputNull.targetPath g true) (fun _ ↦ rfl)
      (nullPath_one g true)) s

/-- Every comparison time fixes the separate ordinary tip. -/
theorem zero (r : I) : parameter g (r, 0) = InputSeedInputNull.tip g false :=
  (wordSwap g).apply_zero r

/-- Every comparison time fixes the separate unit-shifted tip. -/
theorem one (r : I) : parameter g (r, 1) = InputSeedInputNull.tip g true :=
  (wordSwap g).apply_one r

/-- The exact positive strict-unit loop before applying the original input cone homotopy. -/
abbrev originalUnit := (strictLaurentTrack (op Y)).postcomp
  (mappingConeInclusion (InputPositive.strictChart Y))

/-- Original null values under the actual time slice of the fixed input homotopy. -/
theorem null_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (nullPath g e r s) x =
      ((InputPositive.strictSourceNull Y).postcomp ((InputPositive.coneHomotopy g).at r)).level n
        (s, x) :=
  InputSeedInputNull.native g e n r s x

/-- The original Laurent inclusion law acts on the entire strict-unit product. -/
theorem unit_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (unitPath g r s) x =
      ((originalUnit (Y := Y)).postcomp ((InputPositive.coneHomotopy g).at r)).level n (s, x) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _ (InputSeedInputUnitProduct.parameter g (r, s))) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion]
  change (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
    (pointwisePrespectrumFamily (laurentRef g) n
      (CommonReferenceNerve.parameter (laurentRef g) (InputSeedInputUnitProduct.nodes g)
        (InputSeedInputUnitProduct.scalar (r, s))) x) = _
  rw [pointwisePrespectrumFamily_parameter]
  exact congrArg ((mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n)
    (InputSeedInputUnitProduct.native g n r s x)

/-- Both whole null sheets and the unit product recover the original positive seed action. -/
theorem positive_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (parameter g (r, s)) x =
      (InputPositive.coneHomotopy g).level n
        (r, Path.toContinuousMap ((InputPositive.strictSeed Y).map n x) s) := by
  change InputSeedInputNull.nativeEval g n
    (((nullSwap g false).symm.trans ((unitSwap g).trans (nullSwap g true))) (s, r)) x =
      ((InputPositive.coneHomotopy g).at r).map n
        (((originalUnit (Y := Y)).conjugateToZero (InputPositive.strictSourceNull Y)).level n
          (s, x))
  unfold Homotopy.conjugateToZero
  let ev := fun z : Carrier g ↦ InputSeedInputNull.nativeEval g n z x
  let out := ((InputPositive.coneHomotopy g).at r).map n
  exact trans_value (nullSwap g false).symm ((unitSwap g).trans (nullSwap g true))
    (InputPositive.strictSourceNull Y).symm
    ((originalUnit (Y := Y)).trans (InputPositive.strictSourceNull Y)) n x ev out r
    (fun t ↦ null_native g false n r (unitInterval.symm t) x)
    (fun t ↦ trans_value (unitSwap g) (nullSwap g true)
      (originalUnit (Y := Y)) (InputPositive.strictSourceNull Y) n x ev out r
      (fun v ↦ unit_native g n r v x) (fun v ↦ null_native g true n r v x) t) s

/-- Every native point is exactly the fixed whole input homotopy at the original strict seed. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.inputFirst g).level n (r, x)) s := by
  rw [positive_native]
  refine (InputPositive.coneHomotopy_factor g n r
    (Path.toContinuousMap ((InputPositive.strictSeed Y).map n x) s)).trans ?_
  have h := congrArg (fun f ↦ Path.toContinuousMap (f.map n x) s)
    (InputPositive.strictSeed_factor Y)
  change (InputPositive.strictInclusion Y).map n
    (Path.toContinuousMap ((InputPositive.strictSeed Y).map n x) s) =
    Path.toContinuousMap ((GlobalBassEvaluation.strictSeed Y).map n x) s at h
  rw [h]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputFace
