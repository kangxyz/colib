/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackCoordinateChange
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.TransposeSign

/-!
# Interchange of two independent original self-tracks

A pointwise interchange square of four actual prespectrum self-tracks gives
anti-commuting finite homotopy operations in input degree at least two. The
proof normalizes the tracks along distinct original spatial coordinates. Their
literal normalized cubes differ by the transposition of the two track times.
The supplied square contains both independent homotopies, with no structure
clock substituted for either one.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackInterchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology

/-- The spatial coordinate used by the original inverse-prefix cancellation. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def selfTrackCancellationCoordinate (r s : unitInterval) : unitInterval :=
  unitInterval.symm ⟨Path.Homotopy.reflTransSymmAux (unitInterval.symm r, s),
    Path.Homotopy.reflTransSymmAux_mem_I (unitInterval.symm r, s)⟩

/-- The first-half interval coordinate in the original normalization. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def selfTrackNormalizationLeft (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    unitInterval := ⟨2 * t, by constructor <;> linarith [t.property.1]⟩

/-- The second-half interval coordinate in the original normalization. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def selfTrackNormalizationRight (t : unitInterval) (h : ¬(t : ℝ) ≤ 1 / 2) :
    unitInterval := ⟨2 * t - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩

/-- Pointwise sampling of original time and space through both cancellations.
This selector is used only for evaluation, without asserting its continuity. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def selfTrackNormalizationSample (t s : unitInterval) : unitInterval × unitInterval :=
  if ht : (t : ℝ) ≤ 1 / 2 then
    (0, selfTrackCancellationCoordinate (unitInterval.symm (selfTrackNormalizationLeft t ht)) s)
  else
    let r := selfTrackNormalizationRight t ht
    if hr : (r : ℝ) ≤ 1 / 2 then
      if hs : (s : ℝ) ≤ 1 / 2 then
        (0, unitInterval.symm (selfTrackNormalizationLeft s hs))
      else (selfTrackNormalizationLeft r hr, selfTrackNormalizationRight s hs)
    else (0, selfTrackCancellationCoordinate (selfTrackNormalizationRight r hr) s)

/-- Normalization samples exactly the original self-track, including its endpoints. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem loopNormalizedSelfTrack_sample {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) (α : Path γ γ) (t s : unitInterval) :
    loopNormalizedSelfTrack γ α t s =
      α (selfTrackNormalizationSample t s).1 (selfTrackNormalizationSample t s).2 := by
  have hc (r s : unitInterval) :
      loopInversePrefixCancellation γ r s = γ (selfTrackCancellationCoordinate r s) := rfl
  simp only [loopNormalizedSelfTrack, Path.trans_apply, Path.cast_coe, Path.map_coe,
    Function.comp_apply, Path.symm_apply, loopLeftTranslationEquiv_apply,
    selfTrackNormalizationSample, selfTrackNormalizationLeft, selfTrackNormalizationRight]
  split_ifs with ht hr hs
  · rw [α.source]
    exact hc _ _
  · rw [α.source]
    simp only [Path.trans_apply, dite_eq_left hs, Path.symm_apply, Function.comp_apply]
  · simp only [Path.trans_apply, dite_eq_right hs]
  · rw [α.source]
    exact hc _ _

/-- The normalized cube path changes only its displayed first spatial coordinate. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopNormalizedSelfTrackPath_sample {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) (α : Path p p)
    (t : unitInterval) (z : Fin (m + 1) → unitInterval) :
    genLoopNormalizedSelfTrackPath m p α t z =
      α (selfTrackNormalizationSample t (z 0)).1
        (Function.update z 0 (selfTrackNormalizationSample t (z 0)).2) := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  change (loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
    (α.map L.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2) = _
  rw [loopNormalizedSelfTrack_sample]
  change α _ (Cube.insertAt 0 (_, (Cube.splitAt 0 z).2)) = _
  rw [cube_insertAt_splitAt]

namespace LoopPrespectrum
variable {E F G K : LoopPrespectrum.{u}}
variable {f : E ⟶ F} {g : E ⟶ G} {f' : G ⟶ K} {g' : F ⟶ K}

/-- The default cube samples the actual homotopy on the first original spatial line. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCube_sample (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n))
    (z : Fin (m + 2) → unitInterval) :
    genLoopNormalizedSelfTrackCube m _ (H.genLoopPath n p) z =
      H.level n ((selfTrackNormalizationSample (z 0) (Fin.tail z 0)).1,
        p (Function.update (Fin.tail z) 0
          (selfTrackNormalizationSample (z 0) (Fin.tail z 0)).2)) := by
  rw [genLoopNormalizedSelfTrackCube_apply, genLoopNormalizedSelfTrackPath_sample]
  rfl

/-- Normalize along a chosen nonfirst original coordinate, restoring the spatial order. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def Homotopy.genLoopNormalizedSelfTrackCubeAt (H : Homotopy f f) (n m : ℕ)
    (i : Fin (m + 2)) (hi : (0 : Fin (m + 2)) ≠ i)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    GenLoop (Fin (m + 3)) (F.space n) (F.point n) :=
  transposeGenLoop (0 : Fin (m + 2)).succ i.succ
    (fun h ↦ hi (Fin.succ_inj.mp h))
    (genLoopNormalizedSelfTrackCube (m + 1) _
      (H.genLoopPath n (transposeGenLoop 0 i hi p)))

/-- Chosen-coordinate normalization retains literal track time and all other coordinates. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCubeAt_sample (H : Homotopy f f) (n m : ℕ)
    (i : Fin (m + 2)) (hi : (0 : Fin (m + 2)) ≠ i)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n))
    (z : Fin (m + 3) → unitInterval) :
    H.genLoopNormalizedSelfTrackCubeAt n m i hi p z =
      H.level n ((selfTrackNormalizationSample (z 0) (Fin.tail z i)).1,
        p (Function.update (Fin.tail z) i
          (selfTrackNormalizationSample (z 0) (Fin.tail z i)).2)) := by
  change genLoopNormalizedSelfTrackCube (m + 1) _ _
    (cubeCoordinateSwap (0 : Fin (m + 2)).succ i.succ z) = _
  rw [H.genLoopNormalizedSelfTrackCube_sample, cubeCoordinateSwap_succ_zero,
    cubeCoordinateSwap_succ_tail]
  have hs : cubeCoordinateSwap 0 i (Fin.tail z) 0 = Fin.tail z i := by
    simp [cubeCoordinateSwap]
  rw [hs]
  change H.level n (_, p (cubeCoordinateSwap 0 i (Function.update
    (cubeCoordinateSwap 0 i (Fin.tail z)) 0 _))) = _
  rw [cubeCoordinateSwap_update_swap_left 0 i hi]

set_option backward.isDefEq.respectTransparency.types false in
/-- Changing the normalization coordinate leaves the original finite operation unchanged. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCubeAt_class (H : Homotopy f f) (n m : ℕ)
    (i : Fin (m + 2)) (hi : (0 : Fin (m + 2)) ≠ i)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    (⟦H.genLoopNormalizedSelfTrackCubeAt n m i hi p⟧ :
      HomotopyGroup.Pi (m + 3) (F.space n) (F.point n)) =
        H.homotopyClassOperation n (m + 1) ⟦p⟧ := by
  have hinv (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
      H.homotopyClassOperationHom n m a⁻¹ = (H.homotopyClassOperationHom n m a)⁻¹ :=
    map_inv (H.homotopyClassOperationHom n m) a
  have hinput : genLoopSelfTrackClass (m + 1) _
      (H.genLoopPath n (transposeGenLoop 0 i hi p)) =
        (H.homotopyClassOperation n (m + 1) ⟦p⟧)⁻¹ :=
    (congrArg (H.homotopyClassOperation n (m + 1))
      (transposeGenLoop_class 0 i hi p)).trans (hinv ⟦p⟧)
  exact (transposeGenLoop_class (0 : Fin (m + 2)).succ i.succ
    (fun h ↦ hi (Fin.succ_inj.mp h)) _).trans
      ((congrArg (fun a : HomotopyGroup.Pi (m + 3) (F.space n) (F.point n) ↦ a⁻¹)
        ((genLoopNormalizedSelfTrackCube_class (m + 1) _ _).trans hinput)).trans
          (inv_inv (H.homotopyClassOperation n (m + 1) ⟦p⟧)))

variable (H : Homotopy f f) (J : Homotopy g g)
    (H' : Homotopy f' f') (J' : Homotopy g' g')
    (h : ∀ n s t x, H'.level n (s, J.level n (t, x)) =
      J'.level n (t, H.level n (s, x)))

include h

/-- Independent normalizations interchange literally after swapping their two track times. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCube_interchange (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    J'.genLoopNormalizedSelfTrackCubeAt n (m + 1) (1 : Fin (m + 2)).succ
        (Fin.succ_ne_zero _).symm
        (genLoopNormalizedSelfTrackCube (m + 1) _ (H.genLoopPath n p)) =
      transposeGenLoop (0 : Fin (m + 4)) 1 Fin.zero_ne_one
        (H'.genLoopNormalizedSelfTrackCubeAt n (m + 1) 1 Fin.zero_ne_one
          (J.genLoopNormalizedSelfTrackCubeAt n m 1 Fin.zero_ne_one p)) := by
  ext z
  let x := Fin.tail (Fin.tail z)
  let a := selfTrackNormalizationSample (z 1) (x 0)
  let b := selfTrackNormalizationSample (z 0) (x 1)
  have hleft : J'.genLoopNormalizedSelfTrackCubeAt n (m + 1)
      (1 : Fin (m + 2)).succ (Fin.succ_ne_zero _).symm
      (genLoopNormalizedSelfTrackCube (m + 1) _ (H.genLoopPath n p)) z =
      J'.level n (b.1, H.level n (a.1,
        p (Function.update (Function.update x 1 b.2) 0 a.2))) := by
    rw [J'.genLoopNormalizedSelfTrackCubeAt_sample, H.genLoopNormalizedSelfTrackCube_sample]
    simp only [Function.update_of_ne (Fin.succ_ne_zero _).symm, Fin.tail_update_succ,
      Function.update_of_ne Fin.zero_ne_one]
    rfl
  have hright : H'.genLoopNormalizedSelfTrackCubeAt n (m + 1) 1 Fin.zero_ne_one
      (J.genLoopNormalizedSelfTrackCubeAt n m 1 Fin.zero_ne_one p)
      (cubeCoordinateSwap 0 1 z) =
      H'.level n (a.1, J.level n (b.1,
        p (Function.update (Function.update x 0 a.2) 1 b.2))) := by
    rw [H'.genLoopNormalizedSelfTrackCubeAt_sample, J.genLoopNormalizedSelfTrackCubeAt_sample]
    have hu (w : Fin (m + 3) → unitInterval) (r : unitInterval) :
        Fin.tail (Function.update w 1 r) = Function.update (Fin.tail w) 0 r :=
      Fin.tail_update_succ w 0 r
    simp only [Function.update_of_ne Fin.zero_ne_one, hu,
      Function.update_of_ne Fin.zero_ne_one.symm, cubeCoordinateSwap_zero_one_tail_tail]
    simp only [cubeCoordinateSwap]
    rfl
  rw [Function.update_comm Fin.zero_ne_one.symm] at hleft
  exact hleft.trans ((h n a.1 b.1 _).symm.trans hright.symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The two original finite self-track operations anti-commute by the actual interchange square. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_interchange_sign (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    J'.homotopyClassOperation n (m + 2) (H.homotopyClassOperation n (m + 1) a) =
      (H'.homotopyClassOperation n (m + 2) (J.homotopyClassOperation n (m + 1) a))⁻¹ := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [H.homotopyClassOperation_mk,
      ← genLoopNormalizedSelfTrackCube_class (m + 1) _ (H.genLoopPath n p),
      ← J'.genLoopNormalizedSelfTrackCubeAt_class n (m + 1) (1 : Fin (m + 2)).succ
        (Fin.succ_ne_zero _).symm,
      H.genLoopNormalizedSelfTrackCube_interchange J H' J' h]
    refine (transposeGenLoop_class (0 : Fin (m + 4)) 1 Fin.zero_ne_one _).trans ?_
    apply congrArg (fun b : HomotopyGroup.Pi (m + 4) (K.space n) (K.point n) ↦ b⁻¹)
    exact (H'.genLoopNormalizedSelfTrackCubeAt_class n (m + 1) 1 Fin.zero_ne_one _).trans
      (congrArg (H'.homotopyClassOperation n (m + 2))
        (J.genLoopNormalizedSelfTrackCubeAt_class n m 1 Fin.zero_ne_one p))

end LoopPrespectrum
end Topology

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.homotopyClassOperation_interchange_sign
