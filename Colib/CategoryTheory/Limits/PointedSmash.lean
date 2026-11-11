/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Smash products under a terminal object

The two axes of the binary product are collapsed to the same terminal
object. The resulting pointed object retains the literal quotient map
from the binary product and its universal property.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Under

open Limits

variable {C : Type u} [Category.{v} C] [HasTerminal C]
  [HasBinaryProducts C] [HasBinaryCoproducts C]

/-- The two inclusions of the coordinate axes determined by the given points. -/
def axesToProduct (X Y : Under (⊤_ C)) : X.right ⨿ Y.right ⟶ X.right ⨯ Y.right :=
  coprod.desc
    (prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom))
    (prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right))

@[reassoc]
theorem axesToProduct_naturality {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    axesToProduct X Y ≫ prod.map f.right g.right =
      coprod.map f.right g.right ≫ axesToProduct X' Y' := by
  apply coprod.hom_ext <;> apply prod.hom_ext <;> simp [axesToProduct, Category.assoc]

variable [HasPushouts C]

/-- The pointed pushout collapsing both axes of the binary product. -/
def smash (X Y : Under (⊤_ C)) : Under (⊤_ C) :=
  Under.mk (pushout.inr (axesToProduct X Y) (terminal.from (X.right ⨿ Y.right)))

/-- The quotient map from the binary product to the underlying smash object. -/
def toSmash (X Y : Under (⊤_ C)) : X.right ⨯ Y.right ⟶ (smash X Y).right :=
  pushout.inl (axesToProduct X Y) (terminal.from (X.right ⨿ Y.right))

@[reassoc]
theorem axesToProduct_toSmash (X Y : Under (⊤_ C)) :
    axesToProduct X Y ≫ toSmash X Y = terminal.from (X.right ⨿ Y.right) ≫ (smash X Y).hom :=
  pushout.condition

@[reassoc (attr := simp)]
theorem leftAxis_toSmash (X Y : Under (⊤_ C)) :
    prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom) ≫ toSmash X Y =
      terminal.from X.right ≫ (smash X Y).hom := by
  simpa [axesToProduct, Category.assoc] using
    congrArg (fun f => coprod.inl ≫ f) (axesToProduct_toSmash X Y)

@[reassoc (attr := simp)]
theorem rightAxis_toSmash (X Y : Under (⊤_ C)) :
    prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) ≫ toSmash X Y =
      terminal.from Y.right ≫ (smash X Y).hom := by
  simpa [axesToProduct, Category.assoc] using
    congrArg (fun f => coprod.inr ≫ f) (axesToProduct_toSmash X Y)

/-- A map of smash products induced by two pointed maps. -/
def smashMap {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') : smash X Y ⟶ smash X' Y' :=
  Under.homMk
    (pushout.map (axesToProduct X Y) (terminal.from _) (axesToProduct X' Y') (terminal.from _)
      (prod.map f.right g.right) (𝟙 _) (coprod.map f.right g.right)
      (axesToProduct_naturality f g) (by simp)) (by simp [smash, pushout.map])

@[reassoc (attr := simp)]
theorem toSmash_smashMap {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    toSmash X Y ≫ (smashMap f g).right =
      prod.map f.right g.right ≫ toSmash X' Y' := by
  exact pushout.inl_desc _ _ _

/-- A pointed map from a smash product is determined on the product. -/
theorem smash_hom_ext {X Y Z : Under (⊤_ C)} {f g : smash X Y ⟶ Z}
    (h : toSmash X Y ≫ f.right = toSmash X Y ≫ g.right) : f = g := by
  apply (Under.forget (⊤_ C)).map_injective
  apply pushout.hom_ext
  · exact h
  · exact (Under.w f).trans (Under.w g).symm

@[simp]
theorem smashMap_id (X Y : Under (⊤_ C)) : smashMap (𝟙 X) (𝟙 Y) = 𝟙 (smash X Y) := by
  apply smash_hom_ext
  simp

theorem smashMap_comp {X X' X'' Y Y' Y'' : Under (⊤_ C)}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    smashMap f g ≫ smashMap f' g' = smashMap (f ≫ f') (g ≫ g') := by
  apply smash_hom_ext
  simp only [Under.comp_right, toSmash_smashMap_assoc, toSmash_smashMap]
  rw [← Category.assoc, prod.map_map]

/-- The pointed restriction to a slice of the product specified by a point of the second factor. -/
def smashRightPoint (X Y : Under (⊤_ C)) (p : (⊤_ C) ⟶ Y.right) : X ⟶ smash X Y :=
  Under.homMk (prod.lift (𝟙 X.right) (terminal.from X.right ≫ p) ≫ toSmash X Y) (by
    have ht : terminal.from (⊤_ C) = 𝟙 (⊤_ C) := terminalIsTerminal.hom_ext _ _
    have h : X.hom ≫ prod.lift (𝟙 X.right) (terminal.from X.right ≫ p) =
        p ≫ prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) := by
      apply prod.hom_ext <;> simp [ht]
    rw [← Category.assoc, h, Category.assoc, rightAxis_toSmash]
    simp [ht])

@[reassoc]
theorem smashRightPoint_naturality {X X' Y : Under (⊤_ C)}
    (f : X ⟶ X') (p : (⊤_ C) ⟶ Y.right) :
    smashRightPoint X Y p ≫ smashMap f (𝟙 Y) = f ≫ smashRightPoint X' Y p := by
  apply (Under.forget (⊤_ C)).map_injective
  change (_ ≫ toSmash X Y) ≫ (smashMap f (𝟙 Y)).right =
    f.right ≫ (_ ≫ toSmash X' Y)
  rw [Category.assoc, toSmash_smashMap, ← Category.assoc, ← Category.assoc]
  congr 1
  apply prod.hom_ext <;> simp

end CategoryTheory.Under
