/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.HomotopyComposition
public import Colib.Topology.Prespectrum.HomotopySquare

/-! # Pasting along the path coordinate of moving prespectrum squares

Pasting, reversal and postcomposition retain the entire moving family. Replacing its four
boundary tracks by full-level identities retains the same square at each independent parameter.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/HomotopySquareComposition.lean:32-136`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.Homotopy.Square

/-- Paste two whole moving squares in the original path coordinate. -/
def pastePaths {E F : LoopPrespectrum.{u}}
    {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (S : H₀.Square H₁ L M) (T : K₀.Square K₁ M N) :
    (H₀.trans K₀).Square (H₁.trans K₁) L N := by
  let swapSquare {a₀ b₀ a₁ b₁ : E ⟶ F}
      {A₀ : Homotopy a₀ b₀} {A₁ : Homotopy a₁ b₁}
      {B : Homotopy a₀ a₁} {C : Homotopy b₀ b₁}
      (V : A₀.Square A₁ B C) (n : ℕ) :
      (B.level n).Homotopy (C.level n) := {
    toFun := fun z ↦ V.level n (z.2.1, (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := V.left n z.1 z.2
    map_one_left z := V.right n z.1 z.2 }
  let joint n := (swapSquare S n).trans (swapSquare T n)
  refine {
    level := fun n ↦ ⟨fun z ↦ joint n (z.2.1, (z.1, z.2.2)), by fun_prop⟩
    at_zero := ?_
    at_one := ?_
    left := ?_
    right := ?_
    at_point := ?_
    comm := ?_ }
  · intro n s x
    change ((swapSquare S n).trans (swapSquare T n)) (s, (0, x)) =
      ((H₀.levelHomotopy n).trans (K₀.levelHomotopy n)) (s, x)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact S.at_zero n _ x
    · exact T.at_zero n _ x
  · intro n s x
    change ((swapSquare S n).trans (swapSquare T n)) (s, (1, x)) =
      ((H₁.levelHomotopy n).trans (K₁.levelHomotopy n)) (s, x)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact S.at_one n _ x
    · exact T.at_one n _ x
  · intro n r x
    exact (joint n).apply_zero (r, x)
  · intro n r x
    exact (joint n).apply_one (r, x)
  · intro n r s
    change ((swapSquare S n).trans (swapSquare T n)) (s, (r, E.point n)) = _
    rw [ContinuousMap.Homotopy.trans_apply]
    split
    · exact S.at_point n r _
    · exact T.at_point n r _
  · intro n r s x t
    change ((swapSquare S (n + 1)).trans (swapSquare T (n + 1)))
      (s, (r, E.structureMap n x t)) =
        F.structureMap n (((swapSquare S n).trans (swapSquare T n)) (s, (r, x))) t
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split
    · exact S.comm n r _ x t
    · exact T.comm n r _ x t

/-- Reverse both path faces of a moving square. -/
def reversePaths {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M) : H₀.symm.Square H₁.symm M L where
  level n := ⟨fun z ↦ S.level n (z.1, (unitInterval.symm z.2.1, z.2.2)), by fun_prop⟩
  at_zero n s x := S.at_zero n (unitInterval.symm s) x
  at_one n s x := S.at_one n (unitInterval.symm s) x
  left n r x := by simpa using S.right n r x
  right n r x := by simpa using S.left n r x
  at_point n r s := S.at_point n r (unitInterval.symm s)
  comm n r s x t := S.comm n r (unitInterval.symm s) x t

/-- Postcomposition retains the entire joint square and its four original boundary tracks. -/
def postcompose {E F G : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M) (k : F ⟶ G) :
    (H₀.postcomp k).Square (H₁.postcomp k) (L.postcomp k) (M.postcomp k) where
  level n := ⟨fun z ↦ k.map n (S.level n z), by fun_prop⟩
  at_zero n s x := congrArg (k.map n) (S.at_zero n s x)
  at_one n s x := congrArg (k.map n) (S.at_one n s x)
  left n r x := congrArg (k.map n) (S.left n r x)
  right n r x := congrArg (k.map n) (S.right n r x)
  at_point n r s := (congrArg (k.map n) (S.at_point n r s)).trans (k.map_point n)
  comm n r s x t := (congrArg (k.map (n + 1)) (S.comm n r s x t)).trans
    (congrArg (fun p ↦ p t) (k.comm n (S.level n (r, (s, x)))))

/-- Full-level boundary identities change only the specified arrow transports of a square. -/
def ofBoundaryLevels {E F : LoopPrespectrum.{u}}
    {f₀ g₀ f₁ g₁ f₀' g₀' f₁' g₁' : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M)
    (H₀' : Homotopy f₀' g₀') (H₁' : Homotopy f₁' g₁')
    (L' : Homotopy f₀' f₁') (M' : Homotopy g₀' g₁')
    (h₀ : ∀ n, H₀'.level n = H₀.level n) (h₁ : ∀ n, H₁'.level n = H₁.level n)
    (hL : ∀ n, L'.level n = L.level n) (hM : ∀ n, M'.level n = M.level n) :
    H₀'.Square H₁' L' M' where
  level := S.level
  at_zero n s x := (S.at_zero n s x).trans (DFunLike.congr_fun (h₀ n).symm (s, x))
  at_one n s x := (S.at_one n s x).trans (DFunLike.congr_fun (h₁ n).symm (s, x))
  left n r x := (S.left n r x).trans (DFunLike.congr_fun (hL n).symm (r, x))
  right n r x := (S.right n r x).trans (DFunLike.congr_fun (hM n).symm (r, x))
  at_point := S.at_point
  comm := S.comm

end Topology.LoopPrespectrum.Homotopy.Square
