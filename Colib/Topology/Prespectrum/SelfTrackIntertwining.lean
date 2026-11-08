/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackRelativeHomotopy

/-! # Intertwined original self-tracks give the same normalized operations

The underlying original maps may differ. A supplied comparison track and a
whole relative intertwining square transport the actual loop base point by
its own conjugacy. The fixed-cube normalization removes precisely that
conjugacy; no equality of ordinary induced K-maps is used.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackIntertwining.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
variable (H : Homotopy f f) (K : Homotopy g g) (C : Homotopy f g)
variable (J : (H.trans C).RelHomotopy (C.trans K))
include J

/-- The original intertwining square gives conjugacy along the specified comparison cube path. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackIntertwining.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopSelfTrackClass_intertwine (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    genLoopSelfTrackClass m _ (H.genLoopPath n p) =
      genLoopSelfTrackClass m _ (K.genLoopPath n p) := by
  let β := C.genLoopPath n p
  let a : FundamentalGroup _ (GenLoop.postcomp (f.map n) (f.map_point n) p) :=
    FundamentalGroup.fromPath ⟦H.genLoopPath n p⟧
  let b : FundamentalGroup _ (GenLoop.postcomp (g.map n) (g.map_point n) p) :=
    FundamentalGroup.fromPath ⟦K.genLoopPath n p⟧
  let c : FundamentalGroupoid.mk (GenLoop.postcomp (f.map n) (f.map_point n) p) ⟶
      FundamentalGroupoid.mk (GenLoop.postcomp (g.map n) (g.map_point n) p) := ⟦β⟧
  have hp : ((H.trans C).genLoopPath n p).Homotopic ((C.trans K).genLoopPath n p) :=
    ⟨J.genLoopPathHomotopy n m p⟩
  rw [Homotopy.genLoopPath_trans, Homotopy.genLoopPath_trans] at hp
  have hn : a.asHom ≫ c = c ≫ b.asHom := Quotient.sound hp
  have hc : FundamentalGroup.fundamentalGroupMulEquivOfPath β a = b := by
    apply End.ext
    change Groupoid.inv c ≫ (a.asHom ≫ c) = b.asHom
    rw [hn]
    simp
  have ht := genLoopSelfTrackNormalization_transport m β a
  rw [hc] at ht
  exact ht.symm

/-- The actual supplied comparison identifies finite operations, including input Pi-one. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackIntertwining.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_intertwine (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.homotopyClassOperation n m a = K.homotopyClassOperation n m a := by
  induction a using Quotient.inductionOn with
  | h p => exact H.genLoopSelfTrackClass_intertwine K C J n m p

/-- No stable stage, comparison sign or level is changed by the actual intertwining. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackIntertwining.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableStageOperation_intertwine (d : ℤ) (n : ℕ) :
    H.stableStageOperation d n = K.stableStageOperation d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.homotopyClassOperation_intertwine K C J ((-d).toNat + n + 2)
      (d.toNat + n + 1) (Additive.toMul a))

/-- The actual whole intertwining gives equality on the original integer-graded colimits. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackIntertwining.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_intertwine (d : ℤ) :
    H.stableOperation d = K.stableOperation d := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫ H.stableOperation d =
    stableHomotopyι E d n ≫ K.stableOperation d
  rw [H.stableOperation_ι, K.stableOperation_ι, H.stableStageOperation_intertwine K C J]

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.stableOperation_intertwine
