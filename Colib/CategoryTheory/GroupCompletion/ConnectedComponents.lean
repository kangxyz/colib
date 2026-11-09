/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Symmetric
public import Colib.CategoryTheory.GroupCompletion.Switch
public import Colib.CategoryTheory.GroupCompletion.UnitEntry
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.Algebra.Group.Basic

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/ConnectedComponents.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual objects and maps.

# The actual group of categorical components of Grayson completion

Tensoring the original pairs and switching their coordinates descend to an
abelian group on the categorical connected components. The inverse identity is
witnessed by the actual diagonal translation arrow. An original denominator
arrow then expresses every pair as its numerator class minus its denominator
class. No cancellation or groupoid hypothesis on the input category is used.
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
namespace CategoryTheory.GroupCompletion.Localization
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Categorical components of the original completion category. -/
abbrev Components := CategoryTheory.ConnectedComponents (Localization C C)

variable {C}

/-- The component of an original completion object. -/
abbrev componentClass (X : Localization C C) : Components C :=
  CategoryTheory.ConnectedComponents.mk X

omit [SymmetricCategory C] in
/-- Every original arrow preserves its categorical component. -/
theorem componentClass_hom {X Y : Localization C C} (f : X ⟶ Y) :
    componentClass X = componentClass Y := Quotient.sound (Zigzag.of_hom f)

omit [SymmetricCategory C] in
/-- Original isomorphisms in particular preserve the component. -/
theorem componentClass_iso {X Y : Localization C C} (e : X ≅ Y) :
    componentClass X = componentClass Y := componentClass_hom e.hom

omit [SymmetricCategory C] in
/-- Equality of components is exactly an original finite zigzag. -/
theorem componentClass_eq_iff (X Y : Localization C C) :
    componentClass X = componentClass Y ↔ Zigzag X Y := Quotient.eq

/-- The original completion unit represents zero on categorical components. -/
instance componentsZero : Zero (Components C) := ⟨componentClass (unit (C := C))⟩

/-- Tensoring the original pairs induces addition of their categorical components. -/
instance componentsAdd : Add (Components C) :=
  ⟨Quotient.map₂ (fun X Y : Localization C C ↦ X ⊗ Y)
    (fun _ X' hX Y _ hY ↦
      (zigzag_obj_of_zigzag (tensorRight Y) hX).trans
        (zigzag_obj_of_zigzag (tensorLeft X') hY))⟩

/-- Addition is induced by the actual tensor product of pairs. -/
@[simp]
theorem componentClass_tensor (X Y : Localization C C) :
    componentClass (X ⊗ Y) = componentClass X + componentClass Y := rfl

omit [SymmetricCategory C] in
/-- The original unit pair represents zero. -/
@[simp]
theorem componentClass_unit : componentClass (unit (C := C)) = 0 := rfl

/-- The original associator, unitors and braiding give a commutative component monoid. -/
instance componentsAddCommMonoid : AddCommMonoid (Components C) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun X Y Z ↦
    componentClass_iso (α_ X Y Z))
  zero_add a := Quotient.inductionOn a (fun X ↦ componentClass_iso (λ_ X))
  add_zero a := Quotient.inductionOn a (fun X ↦ componentClass_iso (ρ_ X))
  add_comm a b := Quotient.inductionOn₂ a b (fun X Y ↦ componentClass_iso (β_ X Y))
  nsmul := nsmulRec

/-- Switching the original pair coordinates induces negation on components. -/
instance componentsNeg : Neg (Components C) := ⟨switch.mapConnectedComponents⟩

omit [SymmetricCategory C] in
/-- Negation is the actual coordinate-switch functor on components. -/
theorem componentClass_switch (X : Localization C C) :
    componentClass (switch.obj X) = -componentClass X := rfl

/-- The existing diagonal translation arrow proves the inverse identity. -/
theorem components_neg_add_cancel (a : Components C) : -a + a = 0 := by
  induction a using Quotient.inductionOn with
  | h X =>
    change -componentClass X + componentClass X = 0
    exact (add_comm (-componentClass X) (componentClass X)).trans
      (componentClass_hom (inverseArrow X)).symm

/-- The original inverse arrow gives the component monoid its additive group structure. -/
instance componentsAddCommGroup : AddCommGroup (Components C) where
  neg_add_cancel := components_neg_add_cancel
  zsmul := zsmulRec

/-- The actual unit-entry component of an input object. -/
def componentUnitClass (P : C) : Components C := componentClass (unitEntry.obj P)

omit [SymmetricCategory C] in
/-- The unit entrance retains the monoidal unit class. -/
@[simp]
theorem componentUnitClass_unit : componentUnitClass (𝟙_ C) = 0 := rfl

/-- The original unit entrance is additive on tensor objects at the component level. -/
theorem componentUnitClass_tensor (P Q : C) :
    componentUnitClass (P ⊗ Q) = componentUnitClass P + componentUnitClass Q := by
  exact (componentClass_hom (ActionLocalization.ofHom
    (C := C) (X := ((𝟙_ C) ⊗ (𝟙_ C), P ⊗ Q)) (Y := (𝟙_ C, P ⊗ Q))
      ((λ_ (𝟙_ C)).hom, 𝟙 (P ⊗ Q)))).symm

omit [SymmetricCategory C] in
/-- Input isomorphisms induce equality of the original unit-entry components. -/
theorem componentUnitClass_iso {P Q : C} (e : P ≅ Q) :
    componentUnitClass P = componentUnitClass Q :=
  componentClass_hom (unitEntry.map e.hom)

/-- The denominator itself witnesses the relation between a pair and its two unit entries. -/
def componentDenominatorArrow (A B : C) :
    unitEntry.obj B ⟶ (⟨(A, B)⟩ : Localization C C) ⊗ unitEntry.obj A :=
  mkHom A (𝟙 (A ⊗ 𝟙_ C)) (β_ A B).hom

/-- Every original pair is its numerator class minus its denominator class. -/
theorem componentClass_pair_eq_sub (A B : C) :
    componentClass (⟨(A, B)⟩ : Localization C C) =
      componentUnitClass B - componentUnitClass A := by
  apply (eq_sub_iff_add_eq).mpr
  exact (componentClass_hom (componentDenominatorArrow A B)).symm

end CategoryTheory.GroupCompletion.Localization
