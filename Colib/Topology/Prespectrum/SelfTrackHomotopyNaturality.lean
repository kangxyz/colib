/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackNaturality
public import Colib.Topology.Prespectrum.SelfTrackHomotopyAdditivity

/-!
# Original-map naturality of the finite self-track operation

Precomposition retains the original input cube, and postcomposition retains
the original based map on every track and both normalization cancellations.
These are finite equations; no stable operation is defined here.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackHomotopyNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {D E F G : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Postcomposition of the actual H-family induces the original one-higher homotopy map. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_postcomp (H : Homotopy f f) (j : F ⟶ G)
    (n m : ℕ) (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    (H.postcomp j).homotopyClassOperation n m a =
      HomotopyGroup.piMap (m + 1) (j.map n) (j.map_point n) (H.homotopyClassOperation n m a) := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  exact (genLoopSelfTrackClass_naturality (j.map n) (j.map_point n) m _
    (H.genLoopPath n p)).symm

/-- Precomposition applies the original source map to the original sphere representative. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_precomp (H : Homotopy f f) (i : D ⟶ E)
    (n m : ℕ) (a : HomotopyGroup.Pi (m + 1) (D.space n) (D.point n)) :
    (H.precomp i).homotopyClassOperation n m a =
      H.homotopyClassOperation n m (HomotopyGroup.piMap m (i.map n) (i.map_point n) a) := by
  refine Quotient.inductionOn a (fun _ ↦ ?_)
  rfl

/-- The finite homomorphism commutes with the supplied original target map. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperationHom_postcomp (H : Homotopy f f) (j : F ⟶ G)
    (n m : ℕ) :
    (H.postcomp j).homotopyClassOperationHom n m =
      (HomotopyGroup.piMap (m + 2) (j.map n) (j.map_point n)).comp
        (H.homotopyClassOperationHom n m) := by
  ext a
  exact H.homotopyClassOperation_postcomp j n (m + 1) a

/-- The finite homomorphism commutes with the supplied original source map. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperationHom_precomp (H : Homotopy f f) (i : D ⟶ E)
    (n m : ℕ) :
    (H.precomp i).homotopyClassOperationHom n m =
      (H.homotopyClassOperationHom n m).comp
        (HomotopyGroup.piMap (m + 1) (i.map n) (i.map_point n)) := by
  ext a
  exact H.homotopyClassOperation_precomp i n (m + 1) a

end Topology.LoopPrespectrum
