/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.HomotopySquarePathPasting
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam
public import Colib.Topology.Prespectrum.PushoutHomotopySquare
public import Colib.Topology.Prespectrum.PushoutArrowHomotopy

/-!
# Homotopy Square Composition

Support for pasting the actual moving polynomial-span composition square.
Both actual polynomial charts and the whole moving span cylinder are retained.
The native path-pasting and identical-leg moving square are reused.

Adapted from Quillen's `Topology/Prespectrum/HomotopySquareComposition.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
/-- Reversal swaps two composition routes without changing their full levels under transport. -/
theorem Homotopy.reverseTwoRoutes_level {E F : LoopPrespectrum.{u}}
    {f f' a b : E ⟶ F} (H : Homotopy f a) (K : Homotopy f' b) (e : f = f') (n : ℕ) :
    ((K.symm.trans (H.cast e rfl)).symm).level n =
      (H.symm.trans (K.cast e.symm rfl)).level n := by
  rw [Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr <;> rfl

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B A' B' A'' B'' : LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A' ⟶ B') (h : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (c : A' ⟶ A'') (d : B' ⟶ B'')
    (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The original two leg squares paste with their exact geometric order. -/
def identicalLegPastedTrack : Homotopy (f ≫ (b ≫ d)) ((a ≫ c) ≫ h) :=
  ((H.postcomp d).trans ((Homotopy.precomp a K).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)).cast
      (Category.assoc _ _ _) rfl

/-- The complete original composite span cylinder, with literal endpoint transports. -/
def identicalLegActualCompositeTrack :
    Homotopy (f ≫ ((b ≫ d) ≫ inl h h)) (f ≫ ((b ≫ d) ≫ inr h h)) :=
  ((mapSquareHomotopy f f g g a b b H H).postcomp
    (mapOfHomotopies g g h h c d d K K)).cast
      (by simp only [Category.assoc, inl_mapOfHomotopies])
      (by simp only [Category.assoc, inr_mapOfHomotopies])

/-- Literal quotient descent identifies the actual composite cylinder on all generators. -/
theorem identicalLegActualCompositeDesc :
    desc f f ((b ≫ d) ≫ inl h h) ((b ≫ d) ≫ inr h h)
      (identicalLegActualCompositeTrack f g h a b c d H K) =
    mapOfHomotopies f f g g a b b H H ≫
      mapOfHomotopies g g h h c d d K K := by
  apply hom_ext
  · rw [inl_desc, ← Category.assoc, inl_mapOfHomotopies]
    simp only [Category.assoc, inl_mapOfHomotopies]
  · rw [inr_desc, ← Category.assoc, inr_mapOfHomotopies]
    simp only [Category.assoc, inr_mapOfHomotopies]
  · intro n s x
    rfl

/-- Reassociation of all five original cylinder pieces compares actual span-map composition. -/
def identicalLegCompositionPasting :
    (identicalLegActualCompositeTrack f g h a b c d H K).RelHomotopy
      (mapSquareHomotopy f f h h (a ≫ c) (b ≫ d) (b ≫ d)
        (identicalLegPastedTrack f g h a b c d H K)
        (identicalLegPastedTrack f g h a b c d H K)) := by
  let iL := inl h h
  let iR := inr h h
  let P := H.postcomp (d ≫ iL)
  let Q : Homotopy ((a ≫ g) ≫ (d ≫ iL)) ((a ≫ c) ≫ (h ≫ iL)) :=
    (Homotopy.precomp a (K.postcomp iL)).cast
    (by simp only [Category.assoc]) (by simp only [Category.assoc])
  let T := Homotopy.precomp (a ≫ c) (glue h h)
  let U : Homotopy ((a ≫ c) ≫ (h ≫ iR)) ((a ≫ g) ≫ (d ≫ iR)) :=
    (Homotopy.precomp a (K.symm.postcomp iR)).cast
    (by simp only [Category.assoc]) (by simp only [Category.assoc])
  let V := H.symm.postcomp (d ≫ iR)
  have J : (P.trans ((Q.trans (T.trans U)).trans V)).RelHomotopy
      ((P.trans Q).trans (T.trans (U.trans V))) :=
    ((Homotopy.RelHomotopy.refl P).hcomp
      (Homotopy.RelHomotopy.transAssoc Q (T.trans U) V)).trans
      (((Homotopy.RelHomotopy.refl P).hcomp
        ((Homotopy.RelHomotopy.refl Q).hcomp
          (Homotopy.RelHomotopy.transAssoc T U V))).trans
        (Homotopy.RelHomotopy.transAssoc P Q (T.trans (U.trans V))).symm)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    unfold identicalLegActualCompositeTrack mapSquareHomotopy
    change ((_root_.Topology.LoopPrespectrum.Homotopy.trans _ _).postcomp _).level n = _
    rw [Homotopy.postcomp_trans, Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · change (H.postcomp (inl g g ≫ mapOfHomotopies g g h h c d d K K)).level n = P.level n
      rw [inl_mapOfHomotopies]
    · apply Homotopy.trans_level_congr
      · have overlap : (glue g g).postcomp (mapOfHomotopies g g h h c d d K K) =
            mapSquareHomotopy g g h h c d d K K := glue_desc g g _ _ _
        change (Homotopy.precomp a ((glue g g).postcomp
          (mapOfHomotopies g g h h c d d K K))).level n = (Q.trans (T.trans U)).level n
        rw [overlap]
        unfold mapSquareHomotopy
        rw [Homotopy.precomp_trans, Homotopy.precomp_trans]
        apply Homotopy.trans_level_congr
        · rfl
        · apply Homotopy.trans_level_congr <;> rfl
      · change (H.symm.postcomp (inr g g ≫ mapOfHomotopies g g h h c d d K K)).level n = V.level n
        rw [inr_mapOfHomotopies]
  · intro n
    unfold mapSquareHomotopy
    apply Homotopy.trans_level_congr
    · change (((H.postcomp d).trans ((Homotopy.precomp a K).cast _ _)).postcomp iL).level n = _
      rw [Homotopy.postcomp_trans]
      apply Homotopy.trans_level_congr <;> rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · change ((((H.postcomp d).trans ((Homotopy.precomp a K).cast _ _)).symm).postcomp
          iR).level n = _
        rw [Homotopy.symm_trans, Homotopy.postcomp_trans]
        apply Homotopy.trans_level_congr <;> rfl

/-- The whole actual span-map composite compares with the span using the original pasted squares.
Both polynomial charts stay fixed; the entire source cylinder keeps its reparameterization. -/
def identicalLegCompositionHomotopy :
    Homotopy (mapOfHomotopies f f g g a b b H H ≫ mapOfHomotopies g g h h c d d K K)
      (mapOfHomotopies f f h h (a ≫ c) (b ≫ d) (b ≫ d)
        (identicalLegPastedTrack f g h a b c d H K)
        (identicalLegPastedTrack f g h a b c d H K)) :=
  (descHomotopy f f ((b ≫ d) ≫ inl h h) ((b ≫ d) ≫ inr h h)
    (identicalLegCompositionPasting f g h a b c d H K)).cast
      (identicalLegActualCompositeDesc f g h a b c d H K) rfl

end Topology.LoopPrespectrum.HomotopyPushout
