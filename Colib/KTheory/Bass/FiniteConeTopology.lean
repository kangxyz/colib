/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ConeTrack
public import Colib.Topology.Prespectrum.StrictSquareVanishing

/-! # Finite unlooped cone topology

The original unlooped ConeTrack diagram retains T1 separation, genuine chosen-point HEP
and the exact all-point linear vanishing offset through finite iteration.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.FiniteConeTopology
variable {C : Type u} [Category.{v} C]

/-- Finite iteration of the same unlooped cone used by the original cone action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:32"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
def iterate (Q : C ⥤ Arrow (Arrow C)) : ℕ → (C ⥤ LoopPrespectrum.{w}) →
    (C ⥤ LoopPrespectrum.{w})
  | 0, F => F
  | i + 1, F => ConeTrack.diagram Q (iterate Q i F)

/-- One unlooped square cone retains T1 separation at every original level. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:38"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
instance diagramSpaceT1Space (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X m, T1Space ((F.obj X).space m)]
    (X : C) (m : ℕ) : T1Space (((ConeTrack.diagram Q F).obj X).space m) := by
  let S := F.mapArrow.mapArrow.obj (Q.obj X)
  let : T1Space (S.left.left.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).left.left).space m))
  let : T1Space (S.left.right.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).left.right).space m))
  let : T1Space (S.right.left.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).right.left).space m))
  let : T1Space (S.right.right.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).right.right).space m))
  change T1Space ((mappingCone (StrictSquare.comparison S)).space m)
  infer_instance

/-- Every finite unlooped cone retains the original levelwise T1 separation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:54"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
instance iterateSpaceT1Space (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X m, T1Space ((F.obj X).space m)]
    (X : C) (m : ℕ) : T1Space (((iterate Q i F).obj X).space m) := by
  induction i generalizing X m with
  | zero => exact inferInstanceAs (T1Space ((F.obj X).space m))
  | succ i ih =>
    let : ∀ Y k, T1Space (((iterate Q i F).obj Y).space k) := ih
    exact diagramSpaceT1Space Q (iterate Q i F) X m

/-- Genuine point HEP passes through all unlooped cones without a separation premise. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:64"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem iterate_point_homotopyExtensionProperty (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (h : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (X : C) (m : ℕ) : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} (((iterate Q i F).obj X).point m))) := by
  induction i generalizing X m with
  | zero => exact h X m
  | succ i ih =>
    exact StrictSquare.cone_point_homotopyExtensionProperty
      ((iterate Q i F).mapArrow.mapArrow.obj (Q.obj X)) m
      (ih (Q.obj X).left.left m) (ih (Q.obj X).left.right m)
      (ih (Q.obj X).right.left m) (ih (Q.obj X).right.right m)

/-- Every unlooped cone iterate preserves the exact all-point linear vanishing offset. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:79"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem iterate_homotopyGroup_subsingleton (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (h : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : ((iterate Q i F).obj X).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k (((iterate Q i F).obj X).space (n + c + 2)) x) := by
  induction i generalizing X n k with
  | zero => exact hπ X n k hk x
  | succ i ih =>
    let S := (iterate Q i F).mapArrow.mapArrow.obj (Q.obj X)
    have hp := iterate_point_homotopyExtensionProperty Q i F h
    have hs (z : (StrictSquare.span S).space (n + c + 2)) (j : ℕ) (hj : j < n + 2) :
        Subsingleton (HomotopyGroup.Pi j ((StrictSquare.span S).space (n + c + 2)) z) :=
      HomotopyPushout.homotopyGroup_subsingleton S.left.hom S.hom.left _ n
        (hp (Q.obj X).left.left _) (hp (Q.obj X).left.right _)
        (hp (Q.obj X).right.left _)
        (fun a j hj => ih (X := (Q.obj X).left.left) n j hj a)
        (fun b j hj => ih (X := (Q.obj X).left.right) n j hj b)
        (fun d j hj => ih (X := (Q.obj X).right.left) n j hj d) z j hj
    exact ReducedMappingCone.homotopyGroup_subsingleton
      ((StrictSquare.span S).point _) (S.right.right.point _)
      ((StrictSquare.comparison S).map _) ((StrictSquare.comparison S).map_point _)
      (StrictSquare.span_point_homotopyExtensionProperty S _
        (hp (Q.obj X).left.left _) (hp (Q.obj X).left.right _)
        (hp (Q.obj X).right.left _)) (hp (Q.obj X).right.right _) n hs
      (fun d j hj => ih (X := (Q.obj X).right.right) n j hj d) x k hk

end KTheory.Bass.FiniteConeTopology
