/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.GenLoopEvaluation

/-!
# Whole fiber-cube transport along original cube paths

The original cube-space fiber path evaluates to a homotopy relative to the entire spatial
boundary. Varying a supplied null path and moving its source use the actual path-space fiber,
`slideFirst`, and `unpad`. A supplied return to the constant cube uses the original
`iteratedLeftInverseHomotopy`. Every null path and endpoint comparison is retained as data.
No normalization choice, scalar boundary formula, or additional filler is assumed.
-/

/-! Implementation provenance: `Quillen/Topology/HomotopyFiber/GenLoopPathTransport.lean:22-208`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)
local notation "E" => GenLoop (Fin (n + 1)) X x
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)

/-- A cube and its complete displayed null path form the original cube-space fiber point. -/
def genLoopNullPoint (p : E) (P : Path (F p) B) : HomotopyFiber F B :=
  ⟨(p, P.toContinuousMap), P.source, P.target⟩

/-- The original evaluated lift keeps the entire supplied path as its second coordinate. -/
def genLoopNullLift (p : E) (P : Path (F p) B) :
    GenLoop (Fin (n + 1)) (HomotopyFiber f y) (basepoint f y x h) :=
  genLoopEvaluation f y x h n (genLoopNullPoint f y x h n p P)

/-- No null time or spatial coordinate is reparametrized in the evaluated lift. -/
@[simp] theorem genLoopNullLift_path (p : E) (P : Path (F p) B)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (genLoopNullLift f y x h n p P z).val.2 t = P t z := rfl

/-- Evaluate an actual fiber path as a homotopy fixed on the whole spatial boundary. -/
def genLoopEvaluationPath {a b : HomotopyFiber F B} (Q : Path a b) :
    (genLoopEvaluation f y x h n a).val.HomotopyRel
      (genLoopEvaluation f y x h n b).val (Cube.boundary (Fin (n + 1))) where
  toFun sz := genLoopEvaluation f y x h n (Q sz.1) sz.2
  continuous_toFun := Continuous.eval
    ((genLoopEvaluation f y x h n).continuous.comp (Q.continuous.comp continuous_fst))
    continuous_snd
  map_zero_left z := congrArg (fun w ↦ genLoopEvaluation f y x h n w z) Q.source
  map_one_left z := congrArg (fun w ↦ genLoopEvaluation f y x h n w z) Q.target
  prop' s z hz := ((genLoopEvaluation f y x h n (Q s)).property z hz).trans
    ((genLoopEvaluation f y x h n a).property z hz).symm

/-- Endpoint-fixed variation of the whole null path gives a genuine original fiber path. -/
def genLoopNullPointPath (p : E) {P Q : Path (F p) B} (J : P.Homotopy Q) :
    Path (genLoopNullPoint f y x h n p P) (genLoopNullPoint f y x h n p Q) where
  toFun s := ⟨(p, ⟨fun t ↦ J (s, t), by fun_prop⟩), J.source s, J.target s⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact J.continuous
  source' := by
    apply Subtype.ext
    change (p, J.toHomotopy.curry 0) = (p, P.toContinuousMap)
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact J.apply_zero t
  target' := by
    apply Subtype.ext
    change (p, J.toHomotopy.curry 1) = (p, Q.toContinuousMap)
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact J.apply_one t

/-- The full supplied null-path homotopy evaluates relative to every spatial face. -/
def genLoopNullLiftHomotopy (p : E) {P Q : Path (F p) B} (J : P.Homotopy Q) :
    (genLoopNullLift f y x h n p P).val.HomotopyRel
      (genLoopNullLift f y x h n p Q).val (Cube.boundary (Fin (n + 1))) :=
  genLoopEvaluationPath f y x h n (genLoopNullPointPath f y x h n p J)

/-- The source slide uses the actual reverse source path, with no nullity premise on its end. -/
def genLoopSourceIteratedPoint {p q : E} (D : Path p q) (P : Path (F q) B) :
    IteratedFiber F B p :=
  ⟨(genLoopNullPoint f y x h n q P, D.symm.toContinuousMap),
    D.symm.source, D.symm.target⟩

/-- Reverse the original slide, retaining its precise source and target path speeds. -/
def genLoopSourceSlidePath {p q : E} (D : Path p q) (P : Path (F q) B) :
    Path (genLoopNullPoint f y x h n p ((D.map (F).continuous).trans P))
      (projection (projection F B) p
        (unpad F B p (0, genLoopSourceIteratedPoint f y x h n D P))) where
  toFun s := slideFirst F B p (unitInterval.symm s,
    genLoopSourceIteratedPoint f y x h n D P)
  continuous_toFun := (slideFirst F B p).continuous.comp (by fun_prop)
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · change D.symm (unitInterval.symm 0) = p
      simpa only [unitInterval.symm_zero, Path.symm_apply, Function.comp_apply,
        unitInterval.symm_one]
        using D.source
    · apply ContinuousMap.ext
      intro t
      change (((returnPrefix F B p (genLoopSourceIteratedPoint f y x h n D P)
        (unitInterval.symm 0)).map (F).continuous).trans P) t =
          ((D.map (F).continuous).trans P) t
      simp only [Path.trans, Path.coe_mk_mk, Function.comp_apply]
      split_ifs
      · change F (D.symm (unitInterval.symm 0 * unitInterval.symm _)) = F (D _)
        simp only [unitInterval.symm_zero, one_mul, Path.symm_apply, Function.comp_apply,
          unitInterval.symm_symm]
      · rfl
  target' := by
    have hz := congrArg (projection (projection F B) p)
      (slide_zero F B p (genLoopSourceIteratedPoint f y x h n D P))
    change slideFirst F B p (0, genLoopSourceIteratedPoint f y x h n D P) =
      projection (projection F B) p
        (unpad F B p (0, genLoopSourceIteratedPoint f y x h n D P)) at hz
    simpa only [unitInterval.symm_one] using hz

/-- Reversing slide time traverses the original source path in its forward direction. -/
@[simp] theorem genLoopSourceSlidePath_source {p q : E} (D : Path p q)
    (P : Path (F q) B) (s : unitInterval) :
    (genLoopSourceSlidePath f y x h n D P s).val.1 = D s := by
  change D.symm (unitInterval.symm s) = D s
  simp only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]

/-- Remove precisely the original constant prefix after the source slide. -/
def genLoopSourceUnpadPath {p q : E} (D : Path p q) (P : Path (F q) B) :
    Path (projection (projection F B) p
      (unpad F B p (0, genLoopSourceIteratedPoint f y x h n D P)))
      (genLoopNullPoint f y x h n q P) where
  toFun s := projection (projection F B) p
    (unpad F B p (s, genLoopSourceIteratedPoint f y x h n D P))
  continuous_toFun := (projection (projection F B) p).continuous.comp
    ((unpad F B p).continuous.comp (continuous_id.prodMk continuous_const))
  source' := rfl
  target' := congrArg (projection (projection F B) p)
    (unpad_one F B p (genLoopSourceIteratedPoint f y x h n D P))

/-- Transport along the original source path is the reversed slide followed by unpadding. -/
def genLoopSourceTransportPath {p q : E} (D : Path p q) (P : Path (F q) B) :
    Path (genLoopNullPoint f y x h n p ((D.map (F).continuous).trans P))
      (genLoopNullPoint f y x h n q P) :=
  (genLoopSourceSlidePath f y x h n D P).trans (genLoopSourceUnpadPath f y x h n D P)

/-- Source transport retains the entire supplied null and fixes the entire spatial boundary. -/
def genLoopSourceTransportHomotopy {p q : E} (D : Path p q) (P : Path (F q) B) :
    (genLoopNullLift f y x h n p ((D.map (F).continuous).trans P)).val.HomotopyRel
      (genLoopNullLift f y x h n q P).val (Cube.boundary (Fin (n + 1))) :=
  genLoopEvaluationPath f y x h n (genLoopSourceTransportPath f y x h n D P)

/-- The actual return to the constant cube supplies the original iterated-fiber point. -/
def genLoopReturnPoint (p : E) (P : Path (F p) B) (rho : Path p GenLoop.const) :
    IteratedFiber F B GenLoop.const :=
  ⟨(genLoopNullPoint f y x h n p P, rho.toContinuousMap), rho.source, rho.target⟩

/-- The returned loop is exactly the old inverse image-return followed by the whole null. -/
def genLoopReturnedLoop (p : E) (P : Path (F p) B) (rho : Path p GenLoop.const) : Path B B :=
  iteratedToLoops F B GenLoop.const (GenLoop.postcomp_const f h)
    (genLoopReturnPoint f y x h n p P rho)

/-- The source cast is the original based-map equality, with no additional inverse. -/
theorem genLoopReturnedLoop_eq (p : E) (P : Path (F p) B)
    (rho : Path p GenLoop.const) :
    genLoopReturnedLoop f y x h n p P rho =
      (((rho.map (F).continuous).symm.cast
        (GenLoop.postcomp_const f h).symm rfl).trans P) := rfl

/-- The old iterated left-inverse homotopy gives a path in the original cube-space fiber. -/
def genLoopReturnFiberPath (p : E) (P : Path (F p) B) (rho : Path p GenLoop.const) :
    Path (loopInclusion F B GenLoop.const (GenLoop.postcomp_const f h)
      (genLoopReturnedLoop f y x h n p P rho)) (genLoopNullPoint f y x h n p P) :=
  (((iteratedLeftInverseHomotopy F B GenLoop.const
    (GenLoop.postcomp_const f h)).toHomotopy.evalAt
      (genLoopReturnPoint f y x h n p P rho)).map
        (projection (projection F B) GenLoop.const).continuous)

/-- The returned original loop gives the original lifted cube, with all spatial faces fixed. -/
def genLoopReturnHomotopy (p : E) (P : Path (F p) B) (rho : Path p GenLoop.const) :
    (GenLoop.postcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (genLoopOfBasedPath (genLoopReturnedLoop f y x h n p P rho))).val.HomotopyRel
        (genLoopNullLift f y x h n p P).val (Cube.boundary (Fin (n + 1))) :=
  (genLoopEvaluationPath f y x h n (genLoopReturnFiberPath f y x h n p P rho)).cast
    (congrArg Subtype.val (genLoopEvaluation_loopInclusion f y x h n
      (genLoopReturnedLoop f y x h n p P rho))) rfl

/-- Paste the actual return, a supplied complete null comparison, and source transport. -/
def genLoopReturnComparison {p q : E} (D : Path p q) (P : Path (F p) B)
    (N : Path (F q) B) (rho : Path p GenLoop.const)
    (J : P.Homotopy ((D.map (F).continuous).trans N)) :
    (GenLoop.postcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (genLoopOfBasedPath (genLoopReturnedLoop f y x h n p P rho))).val.HomotopyRel
        (genLoopNullLift f y x h n q N).val (Cube.boundary (Fin (n + 1))) :=
  ((genLoopReturnHomotopy f y x h n p P rho).trans
    (genLoopNullLiftHomotopy f y x h n p J)).trans
      (genLoopSourceTransportHomotopy f y x h n D N)

end Topology.HomotopyFiber

attribute [colib_ref "quillen"
    "Quillen/Topology/HomotopyFiber/GenLoopPathTransport.lean:22-208"
    "adaptation"
    "Actual path-space fiber evaluation with every original spatial coordinate and path time"]
  Topology.HomotopyFiber.genLoopReturnHomotopy
  Topology.HomotopyFiber.genLoopReturnComparison
