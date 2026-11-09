/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackOperation
public import Colib.Topology.Homotopy.HomotopyGroup.LoopNormalizationProduct
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackKOne

/-!
# Source additivity of the original degree-zero self-track operation

The original operation on Pi one is a homomorphism when the actual loop action
on Pi two is trivial. The proof retains the genuine normalized tracks and their
inverse relative to the spatial-first loop normalization.

Implementation provenance: `Quillen/Topology/HomotopyGroups/SelfTrackOperation.lean:228-324`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open HomotopyGroup
open scoped Topology unitInterval
universe u
namespace Topology.IdentityTrack
variable {X : Type u} [TopologicalSpace X] {x : X}

private theorem normalization_congr {p q : Path x x} (hp : p = q)
    (α : Path p p) (β : Path q q) (hα : ∀ t, α t = β t) :
    loopKOneNormalization p (FundamentalGroup.fromPath ⟦α⟧) =
      loopKOneNormalization q (FundamentalGroup.fromPath ⟦β⟧) := by
  subst q
  have h : α = β := Path.ext (funext hα)
  subst β
  rfl

private theorem finOne_track_formula (p : GenLoop (Fin 1) X x) (α : Path p p) :
    genLoopSelfTrackClass 0 p α =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        (FundamentalGroup.fromPath ⟦α.map (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧))⁻¹ := by
  let e := genLoopHomeomorphOfUnique (Fin 1) (X := X) (x := x)
  have h := genLoopSelfTrackClass_finOne_eq_inv (e p) (α.map e.continuous)
  have hc := genLoopNormalizedSelfTrackCube_congr 0 (e.symm (e p)) p (e.symm_apply_apply p)
    ((α.map e.continuous).map e.symm.continuous) α (fun t => e.symm_apply_apply (α t))
  have hq := congrArg (fun r : GenLoop (Fin 2) X x => (⟦r⟧ : HomotopyGroup.Pi 2 X x)) hc
  rw [genLoopNormalizedSelfTrackCube_class, genLoopNormalizedSelfTrackCube_class] at hq
  exact hq.symm.trans h

private theorem finOne_transAt (p q : GenLoop (Fin 1) X x) :
    genLoopHomeomorphOfUnique (Fin 1) (GenLoop.transAt 0 p q) =
      (genLoopHomeomorphOfUnique (Fin 1) p).trans
        (genLoopHomeomorphOfUnique (Fin 1) q) :=
  HomotopyGroup.genLoopEquivOfUnique_transAt (Fin 1) q p

/-- The missing one-coordinate product lemma follows from the actual loop
normalization action; the original track-first sign is retained. -/
theorem selfTrack_zero_product
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (p q : GenLoop (Fin 1) X x) (α : Path p p) (β : Path q q) :
    genLoopSelfTrackClass 0 (GenLoop.transAt 0 p q) (genLoopTransAtPath 0 α β) =
      genLoopSelfTrackClass 0 p α * genLoopSelfTrackClass 0 q β := by
  let e := genLoopHomeomorphOfUnique (Fin 1) (X := X) (x := x)
  let M : C(Path x x × Path x x, Path x x) := loopProduct ContinuousMap.fst ContinuousMap.snd
  let A := α.map e.continuous
  let B := β.map e.continuous
  have hc : loopKOneNormalization (e (GenLoop.transAt 0 p q))
      (FundamentalGroup.fromPath ⟦(genLoopTransAtPath 0 α β).map e.continuous⟧) =
        loopKOneNormalization ((e p).trans (e q))
          (FundamentalGroup.fromPath ⟦(A.prod B).map M.continuous⟧) := by
    apply normalization_congr (finOne_transAt p q)
    intro t
    exact finOne_transAt (α t) (β t)
  have hn := hc.trans (normalization_product hs (e p) (e q) A B)
  calc
    _ = (loopKOneNormalization (e (GenLoop.transAt 0 p q))
        (FundamentalGroup.fromPath ⟦(genLoopTransAtPath 0 α β).map e.continuous⟧))⁻¹ :=
      finOne_track_formula _ _
    _ = (loopKOneNormalization (e p) (FundamentalGroup.fromPath ⟦A⟧) *
        loopKOneNormalization (e q) (FundamentalGroup.fromPath ⟦B⟧))⁻¹ :=
      congrArg Inv.inv hn
    _ = (loopKOneNormalization (e p) (FundamentalGroup.fromPath ⟦A⟧))⁻¹ *
        (loopKOneNormalization (e q) (FundamentalGroup.fromPath ⟦B⟧))⁻¹ := by
      rw [mul_inv_rev, mul_comm]
    _ = _ := congrArg₂ (· * ·) (finOne_track_formula p α).symm
      (finOne_track_formula q β).symm

/-- Source degree one is additive once its actual action on Pi two is trivial. -/
theorem operation_mul_zero
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hH : ∀ t, H (t, x) = x)
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (a b : HomotopyGroup.Pi 1 X x) :
    operation H hH 0 (a * b) = operation H hH 0 a * operation H hH 0 b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  refine (congrArg (operation H hH 0)
    (HomotopyGroup.mul_spec (i := (0 : Fin 1)) (p := p) (q := q))).trans ?_
  have ht : track H hH 0 (GenLoop.transAt 0 q p) =
      genLoopTransAtPath 0 (track H hH 0 q) (track H hH 0 p) := by
    ext t s
    change H (t, GenLoop.transAt 0 q p s) =
      GenLoop.transAt 0 (track H hH 0 q t) (track H hH 0 p t) s
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    split_ifs <;> rfl
  exact (congrArg (genLoopSelfTrackClass 0 (GenLoop.transAt 0 q p)) ht).trans
    ((selfTrack_zero_product hs q p _ _).trans (mul_comm _ _))

/-- The actual degree-one source operation with its proved group law. -/
def zeroHom
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hH : ∀ t, H (t, x) = x)
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a) :
    HomotopyGroup.Pi 1 X x →* HomotopyGroup.Pi 2 X x where
  toFun := operation H hH 0
  map_one' := operation_one H hH 0
  map_mul' := operation_mul_zero H hH hs

/-- In source degree one, the track-first operation is the inverse of the
original spatial-first loop normalization, with the actual mapped track. -/
theorem operation_zero_normalization
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hH : ∀ t, H (t, x) = x) (p : GenLoop (Fin 1) X x) :
    operation H hH 0 ⟦p⟧ =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        (FundamentalGroup.fromPath
          ⟦(track H hH 0 p).map (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧))⁻¹ :=
  finOne_track_formula p (track H hH 0 p)

end Topology.IdentityTrack

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/SelfTrackOperation.lean:228-324"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  Topology.IdentityTrack.selfTrack_zero_product
  Topology.IdentityTrack.operation_mul_zero
  Topology.IdentityTrack.zeroHom
  Topology.IdentityTrack.operation_zero_normalization
