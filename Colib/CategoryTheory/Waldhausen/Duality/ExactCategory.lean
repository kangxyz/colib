/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ZeroSquare
public import Colib.CategoryTheory.Waldhausen.Duality.Basic
public import Colib.CategoryTheory.ExactCategory.Isomorphisms

/-! # Opposite Waldhausen structures from genuine exact-category fibrations

Admissible epimorphisms become opposite cofibrations. Their pullback and zero
axioms follow from the exact structure; a genuine pullback gluing theorem for
the selected original weak maps gives the remaining Waldhausen axiom.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Duality/ExactCategory.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C]

/-- The actual weak-map gluing axiom for pullbacks along the selected fibrations. -/
structure HasPullbackGluing (fib weq : MorphismProperty C) : Prop where
  gluing {P X Y Z P' X' Y' Z' : C}
    {i : P ⟶ X} {j : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i' : P' ⟶ X'} {j' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (a : P ⟶ P') (b : X ⟶ X') (d : Y ⟶ Y') (p : Z ⟶ Z') :
    fib f → fib f' → IsPullback i j f g → IsPullback i' j' f' g' →
    i ≫ b = a ≫ i' → j ≫ d = a ≫ j' →
    f ≫ p = b ≫ f' → g ≫ p = d ≫ g' →
    weq b → weq d → weq p → weq a

variable [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (W : Structure C)
  (glue : HasPullbackGluing E.deflation W.weq)

/-- The actual opposite structure, whose cofibrations are the original admissible epis. -/
def exactDualStructure : Structure Cᵒᵖ where
  zero := op (0 : C)
  isZero := (isZero_zero C).op
  cof := E.deflation.op
  weq := W.weq.op
  cof_multiplicative := {
    id_mem := fun X => E.deflation_id X.unop
    comp_mem := fun f g hf hg => E.deflation_comp g.unop f.unop hg hf }
  weq_multiplicative := inferInstance
  cof_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact E.deflation_of_iso (asIso f.unop)
  weq_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact W.weq_iso f.unop inferInstance
  cof_zero X := by
    change E.deflation _
    convert E.deflation_zero X.unop using 1
    exact (isZero_zero C).eq_of_tgt _ _
  pushout_exists i f hi := by
    let : HasPullback i.unop f.unop := E.deflation.hasPullback f.unop hi
    exact ⟨op (pullback i.unop f.unop), (pullback.fst _ _).op,
      (pullback.snd _ _).op, (IsPullback.of_hasPullback i.unop f.unop).op.flip⟩
  cof_pushout hi h := E.deflation.of_isPullback h.unop.flip hi
  gluing := by
    intro A B D P A' B' D' P' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact glue.gluing p.unop b.unop d.unop a.unop hi' hi h'.unop.flip h.unop.flip
      (congrArg Quiver.Hom.unop eg).symm (congrArg Quiver.Hom.unop ej).symm
      (congrArg Quiver.Hom.unop ei).symm (congrArg Quiver.Hom.unop ef).symm hb hd ha

/-- Exact-category kernel–cokernel duality proves the full original grid compatibility. -/
theorem exactDualStructure_compatible (hcof : W.cof = E.inflation) :
    IsCompatibleDual W (exactDualStructure E W glue) where
  weak _ := Iff.rfl
  cofiber i z q s hZ := by
    change (W.cof i ∧ IsPushout i z q s) ↔ (E.deflation q ∧ IsPullback i z q s)
    rw [hcof]
    exact E.inflation_pushout_zero_iff_deflation_pullback hZ

end CategoryTheory.Waldhausen
