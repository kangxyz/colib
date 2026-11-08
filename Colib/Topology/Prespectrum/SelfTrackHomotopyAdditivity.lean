/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackHomotopyClass
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackSpatialProduct

/-!
# Spatial additivity of finite self-track classes in input degree at least two

The original second cube coordinate supplies a spatial product independent of
the first normalization coordinate and track time. The normalized output
retains exactly the library product order. This module claims only a finite
homotopy-group homomorphism; no stable successor or original seed equation is
included.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackHomotopyAdditivity.lean`
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

namespace LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The actual H-family retains the original spatial product through normalization. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyAdditivity.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCube_transAt (H : Homotopy f f)
    (n m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0)
    (p q : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    genLoopNormalizedSelfTrackCube m _ (H.genLoopPath n (GenLoop.transAt i p q)) =
      GenLoop.transAt i.succ
        (genLoopNormalizedSelfTrackCube m _ (H.genLoopPath n p))
        (genLoopNormalizedSelfTrackCube m _ (H.genLoopPath n q)) := by
  have hbase := GenLoop.postcomp_transAt (f.map n) (f.map_point n) i p q
  have htrack : ∀ t, H.genLoopPath n (GenLoop.transAt i p q) t =
      genLoopTransAtPath i (H.genLoopPath n p) (H.genLoopPath n q) t := by
    intro t
    ext z
    change H.level n (t, GenLoop.transAt i p q z) =
      GenLoop.transAt i (H.genLoopPath n p t) (H.genLoopPath n q t) z
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    split_ifs <;> rfl
  exact (genLoopNormalizedSelfTrackCube_congr m _ _ hbase _ _ htrack).trans
    (Topology.genLoopNormalizedSelfTrackCube_transAt m i hi _ _ _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The finite quotient operation preserves the group product in input degree at least two. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyAdditivity.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_mul (H : Homotopy f f) (n m : ℕ)
    (a b : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperation n (m + 1) (a * b) =
      H.homotopyClassOperation n (m + 1) a * H.homotopyClassOperation n (m + 1) b := by
  refine Quotient.inductionOn₂ a b (fun p q ↦ ?_)
  exact (congrArg (H.homotopyClassOperation n (m + 1))
    (HomotopyGroup.mul_spec (i := (1 : Fin (m + 2))) (p := p) (q := q))).trans
      ((genLoopNormalizedSelfTrackCube_class (m + 1) _
        (H.genLoopPath n (GenLoop.transAt 1 q p))).symm.trans
          ((congrArg Quotient.mk' (H.genLoopNormalizedSelfTrackCube_transAt n (m + 1)
            1 (by exact Fin.zero_ne_one.symm) q p)).trans
              ((HomotopyGroup.mul_spec (i := (1 : Fin (m + 2)).succ)).symm.trans
                (congrArg₂ (· * ·)
                  (genLoopNormalizedSelfTrackCube_class (m + 1) _ (H.genLoopPath n p))
                  (genLoopNormalizedSelfTrackCube_class (m + 1) _ (H.genLoopPath n q))))))

/-- The actual finite self-track function is a homomorphism on every input group of degree ≥ 2. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyAdditivity.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def Homotopy.homotopyClassOperationHom (H : Homotopy f f) (n m : ℕ) :
    HomotopyGroup.Pi (m + 2) (E.space n) (E.point n) →*
      HomotopyGroup.Pi (m + 3) (F.space n) (F.point n) where
  toFun := H.homotopyClassOperation n (m + 1)
  map_mul' := H.homotopyClassOperation_mul n m
  map_one' := by
    have h := (H.homotopyClassOperation_mul n m 1 1).symm
    exact mul_left_cancel (show
      H.homotopyClassOperation n (m + 1) 1 * H.homotopyClassOperation n (m + 1) 1 =
        H.homotopyClassOperation n (m + 1) 1 * 1 by
      simpa only [one_mul, mul_one] using h)

/-- The homomorphism is exactly the previously constructed quotient operation. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyAdditivity.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem Homotopy.homotopyClassOperationHom_apply (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperationHom n m a = H.homotopyClassOperation n (m + 1) a := rfl

end LoopPrespectrum
end Topology

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.homotopyClassOperationHom
