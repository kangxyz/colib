/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.PushoutInterchangeIso
public import Colib.Topology.Prespectrum.StrictSquareConeInterchange

/-!
# The original square cone commutes with a pointwise reduced pushout

A span of actual strict squares gives its literal four-corner reduced-pushout
square. The nine-stratum pushout interchange preserves its original constant
comparison. Composing that comparison-arrow isomorphism with the original
cone/pushout interchange gives the original unlooped total-cone isomorphism.
Only the two given square maps are input; no extension or whole-track
compatibility is assumed, and all overlap parameters are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
namespace Pushout
open HomotopyPushout
variable {S₀ S₁ S₂ : Arrow (Arrow LoopPrespectrum.{u})}
  (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)

/-- The original top edge of the pointwise pushout square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:35"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def top : prespectrum f.left.left g.left.left ⟶ prespectrum f.left.right g.left.right :=
  map _ _ _ _ S₀.left.hom S₁.left.hom S₂.left.hom f.left.w g.left.w

/-- The original bottom edge of the pointwise pushout square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:39"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def bottom : prespectrum f.right.left g.right.left ⟶ prespectrum f.right.right g.right.right :=
  map _ _ _ _ S₀.right.hom S₁.right.hom S₂.right.hom f.right.w g.right.w

/-- The original left edge of the pointwise pushout square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:43"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def left : prespectrum f.left.left g.left.left ⟶ prespectrum f.right.left g.right.left :=
  map _ _ _ _ S₀.hom.left S₁.hom.left S₂.hom.left
    (congrArg (fun a => a.left) f.w) (congrArg (fun a => a.left) g.w)

/-- The original right edge of the pointwise pushout square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:48"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def right : prespectrum f.left.right g.left.right ⟶ prespectrum f.right.right g.right.right :=
  map _ _ _ _ S₀.hom.right S₁.hom.right S₂.hom.right
    (congrArg (fun a => a.right) f.w) (congrArg (fun a => a.right) g.w)

/-- The pointwise square commutes on both original inclusions and its full overlap. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:53"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
theorem comm : left f g ≫ bottom f g = top f g ≫ right f g := by
  apply hom_ext
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (HomotopyPushout.left f.right.right g.right.right n)
      (congrArg (fun a => a.map n x) S₁.hom.w)
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (HomotopyPushout.right f.right.right g.right.right n)
      (congrArg (fun a => a.map n x) S₂.hom.w)
  · intro n r x
    exact congrArg (fun y => cylinder f.right.right g.right.right n (r,y))
      (congrArg (fun a => a.map n x) S₀.hom.w)

/-- The literal pointwise original reduced-pushout square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:70"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def square : Arrow (Arrow LoopPrespectrum.{u}) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (top f g)) (g := Arrow.mk (bottom f g))
    (left f g) (right f g) (comm f g))

/-- The three original source-span corners of a strict square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:75"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def sourceCorner (S : Arrow (Arrow LoopPrespectrum.{u})) : Fin 3 → LoopPrespectrum.{u}
  | 0 => S.left.left
  | 1 => S.left.right
  | 2 => S.right.left

/-- The three literal squares in the given span. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:81"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def sourceSquare : Fin 3 → Arrow (Arrow LoopPrespectrum.{u})
  | 0 => S₀
  | 1 => S₁
  | 2 => S₂

/-- The nine original corners form the actual strict span grid. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:87"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def grid : SpanGrid.{u} where
  obj i j := sourceCorner (sourceSquare (S₀ := S₀) (S₁ := S₁) (S₂ := S₂) i) j
  horizontalLeft i := (sourceSquare (S₀ := S₀) (S₁ := S₁) (S₂ := S₂) i).left.hom
  horizontalRight i := (sourceSquare (S₀ := S₀) (S₁ := S₁) (S₂ := S₂) i).hom.left
  verticalLeft
    | 0 => f.left.left
    | 1 => f.left.right
    | 2 => f.right.left
  verticalRight
    | 0 => g.left.left
    | 1 => g.left.right
    | 2 => g.right.left
  left_left := f.left.w.symm
  left_right := (congrArg (fun a => a.left) f.w).symm
  right_left := g.left.w.symm
  right_right := (congrArg (fun a => a.left) g.w).symm

/-- The actual nine-stratum interchange between the two original source spans. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:105"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def spanIso : prespectrum (spanMap f) (spanMap g) ≅ span (square f g) :=
  (grid f g).interchangeIso

/-- The original constant comparison commutes with the entire nine-stratum interchange. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:109"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
theorem spanIso_comparison :
    (spanIso f g).hom ≫ comparison (square f g) =
      spanArrowMap (strictSquareComparisonFunctor.map f) (strictSquareComparisonFunctor.map g) := by
  apply hom_ext
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n r q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl

/-- The actual original comparison arrows are isomorphic by span interchange and identity. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:128"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def comparisonArrowIso :
    Arrow.mk (spanArrowMap (strictSquareComparisonFunctor.map f)
      (strictSquareComparisonFunctor.map g)) ≅ Arrow.mk (comparison (square f g)) :=
  Arrow.isoMk
    (f := Arrow.mk (spanArrowMap (strictSquareComparisonFunctor.map f)
      (strictSquareComparisonFunctor.map g)))
    (g := Arrow.mk (comparison (square f g)))
    (spanIso f g) (Iso.refl _) ((spanIso_comparison f g).trans (Category.comp_id _).symm)

/-- Unlooped total cones commute with the literal pointwise reduced pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquarePushout.lean:138"
  "adaptation" "Original pointwise strict-square pushout and full comparison-arrow isomorphism."]
def totalIso :
    prespectrum (mappingConeMap (strictSquareComparisonFunctor.map f))
      (mappingConeMap (strictSquareComparisonFunctor.map g)) ≅
        mappingCone (comparison (square f g)) :=
  (HomotopyPushout.coneInterchangeIso (strictSquareComparisonFunctor.map f)
    (strictSquareComparisonFunctor.map g)).symm ≪≫
      mappingConeFunctor.mapIso (comparisonArrowIso f g)

end Pushout
end Topology.LoopPrespectrum.StrictSquare
