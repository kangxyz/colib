/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopNormalizedSelfTrackPrefix
public import Colib.Topology.HomotopyFiber.GenLoopPathTransport

/-! # The original normalized self-track and its returned fiber loop

A fine path and its entire coarse return give the displayed inverse-prefix null and fine return.
The old normalized self-track is homotopic to the old returned fiber loop through the original
cancellation naturalities and constructive path associators. All endpoint casts, path times and
spatial boundaries remain explicit. No scalar data or additional comparison is assumed.
-/
/-! Implementation provenance: `Quillen/Topology/HomotopyFiber/GenLoopNormalizedReturn.lean:24-108`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
endpoint casts, cancellations and path orientations are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Return from the actual inverse-prefix endpoint through the original fine cancellation. -/
def genLoopPrefixReturn {x : X} (n : ℕ)
    {a d : GenLoop (Fin (n + 1)) X x} (R : Path a d) :
    Path (GenLoopPrefix.inversePrefix n a d) GenLoop.const :=
  (R.symm.map (GenLoopPrefix.inversePrefix n a).continuous).trans
    (GenLoopPrefix.cancellation n a)

variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)
local notation "E" => GenLoop (Fin (n + 1)) X x
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)

/-- The complete moving coarse return retains the forward inverse-prefix source transport. -/
def genLoopPrefixNull {a d : E} (lambda : Path (F d) (F a)) :
    Path (F (GenLoopPrefix.inversePrefix n a d)) B :=
  ((lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
    (GenLoopPrefix.cancellation n (F a))).cast
      (GenLoopPrefix.inversePrefix_map n f h a d) rfl

/-- Neither the source transport nor the cancellation removes any original null time. -/
theorem genLoopPrefixNull_apply {a d : E} (lambda : Path (F d) (F a)) (t : unitInterval) :
    genLoopPrefixNull f y x h n lambda t =
      ((lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
        (GenLoopPrefix.cancellation n (F a))) t := rfl

/-- The returned loop is the original four-piece word with its exact concatenation speeds. -/
theorem genLoopReturnedLoop_prefix {a d : E} (R : Path a d) (lambda : Path (F d) (F a)) :
    genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R) =
      ((GenLoopPrefix.cancellation n (F a)).symm.trans
        ((R.map (F).continuous).map
          (GenLoopPrefix.inversePrefix n (F a)).continuous)).trans
        ((lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
          (GenLoopPrefix.cancellation n (F a))) := by
  have hk (t : unitInterval) :
      F (GenLoopPrefix.cancellation n a t) = GenLoopPrefix.cancellation n (F a) t :=
    congrArg (fun P ↦ P t) (GenLoopPrefix.cancellation_map n f h a)
  have hp (t : unitInterval) :
      F (GenLoopPrefix.inversePrefix n a (R t)) =
        GenLoopPrefix.inversePrefix n (F a) (F (R t)) :=
    GenLoopPrefix.inversePrefix_map n f h a (R t)
  rw [genLoopReturnedLoop_eq]
  unfold genLoopPrefixReturn
  rw [Path.map_trans, Path.trans_symm]
  simp only [Path.map_symm, Path.symm_symm]
  apply Path.ext
  funext t
  simp only [genLoopPrefixNull, Path.cast_coe, Path.trans_apply, Path.map_coe,
    Path.symm_apply, Function.comp_apply]
  split_ifs
  · exact hk _
  · exact hp _
  · rfl
  · rfl

/-- Original constructive associators compare normalization with the actual returned loop. -/
def genLoopNormalizedReturnHomotopy {a d : E} (R : Path a d) (lambda : Path (F d) (F a)) :
    (genLoopNormalizedSelfTrackPath n (F a) ((R.map (F).continuous).trans lambda)).Homotopy
      (genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R)) := by
  let A := (GenLoopPrefix.cancellation n (F a)).symm
  let P := (R.map (F).continuous).map (GenLoopPrefix.inversePrefix n (F a)).continuous
  let Q := lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous
  let C := GenLoopPrefix.cancellation n (F a)
  have hs : genLoopNormalizedSelfTrackPath n (F a) ((R.map (F).continuous).trans lambda) =
      A.trans ((P.trans Q).trans C) := by
    rw [genLoopNormalizedSelfTrackPath_prefix, Path.map_trans]
  have ht : genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
      (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R) =
        (A.trans P).trans (Q.trans C) :=
    genLoopReturnedLoop_prefix f y x h n R lambda
  exact (((Path.Homotopy.refl A).hcomp (Path.Homotopy.transAssoc P Q C)).trans
    (Path.Homotopy.transAssoc A P (Q.trans C)).symm).cast hs.symm ht.symm

/-- Both interpolation times preserve every original spatial face, including dimension zero. -/
theorem genLoopNormalizedReturnHomotopy_boundary {a d : E}
    (R : Path a d) (lambda : Path (F d) (F a)) (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopNormalizedReturnHomotopy f y x h n R lambda (s, t) z = y :=
  (genLoopNormalizedReturnHomotopy f y x h n R lambda (s, t)).property z hz

end Topology.HomotopyFiber

attribute [colib_ref "quillen"
    "Quillen/Topology/HomotopyFiber/GenLoopNormalizedReturn.lean:24-108"
    "adaptation"
    "Constructive normalized-to-returned fiber loop homotopy with all parameters"]
  Topology.HomotopyFiber.genLoopPrefixReturn
  Topology.HomotopyFiber.genLoopPrefixNull
  Topology.HomotopyFiber.genLoopPrefixNull_apply
  Topology.HomotopyFiber.genLoopReturnedLoop_prefix
  Topology.HomotopyFiber.genLoopNormalizedReturnHomotopy
  Topology.HomotopyFiber.genLoopNormalizedReturnHomotopy_boundary
