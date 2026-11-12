/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmash
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# The wedge presentation of the pointed smash quotient

The two product axes meet at the displayed point. Their wedge maps
monomorphically to the product in an adhesive category. Collapsing
this wedge gives a pushout on the original smash object with its
original quotient and point maps.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasPushouts C]

/-- The wedge of the two product axes, with the points identified. -/
abbrev wedgeAxes (X Y : Under (⊤_ C)) : C :=
  pushout X.hom Y.hom

/-- The map of wedges induced by the actual maps of both pointed factors. -/
def wedgeAxesMap {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    wedgeAxes X Y ⟶ wedgeAxes X' Y' :=
  pushout.map X.hom Y.hom X'.hom Y'.hom f.right g.right (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem inl_wedgeAxesMap {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    pushout.inl X.hom Y.hom ≫ wedgeAxesMap f g = f.right ≫ pushout.inl X'.hom Y'.hom :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_wedgeAxesMap {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    pushout.inr X.hom Y.hom ≫ wedgeAxesMap f g = g.right ≫ pushout.inr X'.hom Y'.hom :=
  pushout.inr_desc _ _ _

variable [HasBinaryProducts C]

private abbrev leftSmashAxis (X Y : Under (⊤_ C)) : X.right ⟶ X.right ⨯ Y.right :=
  prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom)

private abbrev rightSmashAxis (X Y : Under (⊤_ C)) : Y.right ⟶ X.right ⨯ Y.right :=
  prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right)

omit [HasPushouts C] in
private theorem isPullback_smashAxes (X Y : Under (⊤_ C)) :
    IsPullback X.hom Y.hom (leftSmashAxis X Y) (rightSmashAxis X Y) := by
  have ht : terminal.from (⊤_ C) = 𝟙 (⊤_ C) := terminalIsTerminal.hom_ext _ _
  refine IsPullback.mk' (by apply prod.hom_ext <;> simp [ht]) ?_ ?_
  · intro Z a b _ _
    exact terminalIsTerminal.hom_ext a b
  · intro Z a b h
    refine ⟨terminal.from Z, ?_, ?_⟩
    · simpa [Category.assoc] using
        (congrArg (· ≫ (prod.fst : X.right ⨯ Y.right ⟶ X.right)) h).symm
    · simpa [Category.assoc] using
        congrArg (· ≫ (prod.snd : X.right ⨯ Y.right ⟶ Y.right)) h

/-- Include the two actual axes in the product through their wedge. -/
@[no_expose]
def wedgeToProduct (X Y : Under (⊤_ C)) : wedgeAxes X Y ⟶ X.right ⨯ Y.right :=
  (IsPushout.of_hasPushout X.hom Y.hom).desc
    (leftSmashAxis X Y) (rightSmashAxis X Y) (isPullback_smashAxes X Y).w

@[reassoc (attr := simp)]
theorem inl_wedgeToProduct (X Y : Under (⊤_ C)) :
    pushout.inl X.hom Y.hom ≫ wedgeToProduct X Y =
      prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom) :=
  (IsPushout.of_hasPushout X.hom Y.hom).inl_desc
    (leftSmashAxis X Y) (rightSmashAxis X Y) (isPullback_smashAxes X Y).w

@[reassoc (attr := simp)]
theorem inr_wedgeToProduct (X Y : Under (⊤_ C)) :
    pushout.inr X.hom Y.hom ≫ wedgeToProduct X Y =
      prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) :=
  (IsPushout.of_hasPushout X.hom Y.hom).inr_desc
    (leftSmashAxis X Y) (rightSmashAxis X Y) (isPullback_smashAxes X Y).w

/-- The displayed union of the two split monomorphic axes is monomorphic. -/
theorem mono_wedgeToProduct [Adhesive C] (X Y : Under (⊤_ C)) :
    Mono (wedgeToProduct X Y) := by
  let : Mono (leftSmashAxis X Y) := mono_of_mono_fac (prod.lift_fst _ _)
  let : Mono (rightSmashAxis X Y) := mono_of_mono_fac (prod.lift_snd _ _)
  exact (IsPushout.of_hasPushout X.hom Y.hom).desc_mono_of_isPullback
    (isPullback_smashAxes X Y)

/-- The wedge comparison retains both actual maps on product coordinates. -/
@[reassoc]
theorem wedgeToProduct_naturality {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    wedgeToProduct X Y ≫ prod.map f.right g.right =
      wedgeAxesMap f g ≫ wedgeToProduct X' Y' := by
  apply pushout.hom_ext
  · rw [inl_wedgeToProduct_assoc, inl_wedgeAxesMap_assoc, inl_wedgeToProduct]
    apply prod.hom_ext <;> simp [Category.assoc]
  · rw [inr_wedgeToProduct_assoc, inr_wedgeAxesMap_assoc, inr_wedgeToProduct]
    apply prod.hom_ext <;> simp [Category.assoc]

variable [HasBinaryCoproducts C]

/-- Collapsing the wedge is a pushout on the actual smash quotient. -/
theorem smash_isPushout_wedge (X Y : Under (⊤_ C)) :
    IsPushout (wedgeToProduct X Y) (terminal.from (wedgeAxes X Y))
      (toSmash X Y) (smash X Y).hom := by
  refine IsPushout.mk' ?_ ?_ ?_
  · apply pushout.hom_ext <;> simp
  · intro Z f g hf hg
    apply pushout.hom_ext <;> assumption
  · intro Z a b h
    have h' : axesToProduct X Y ≫ a = terminal.from (X.right ⨿ Y.right) ≫ b := by
      apply coprod.hom_ext
      · simpa [axesToProduct, Category.assoc] using
          congrArg (pushout.inl X.hom Y.hom ≫ ·) h
      · simpa [axesToProduct, Category.assoc] using
          congrArg (pushout.inr X.hom Y.hom ≫ ·) h
    exact ⟨pushout.desc a b h', pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

end CategoryTheory.Under
