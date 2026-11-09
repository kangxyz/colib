/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Monoidal

/-!
Implementation provenance: adapted from `Quillen/CategoryTheory/GroupCompletion/Symmetric.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual objects and maps.

# Symmetry of Grayson's multiplication

The original symmetry descends simultaneously in the two coordinates. Its
naturality uses a common braiding of the translating objects.
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory

namespace CategoryTheory.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

@[reassoc]
private lemma interchange_braiding (s t x y : C) :
    tensorμ s t x y ≫ (β_ (s ⊗ x) (t ⊗ y)).hom =
      ((β_ s t).hom ⊗ₘ (β_ x y).hom) ≫ tensorμ t s y x := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding x t, tensorHom_def]

private lemma braiding_coherence {s t x y x' y' : C}
    (f : s ⊗ x ⟶ x') (g : t ⊗ y ⟶ y') :
    (β_ s t).hom ▷ (x ⊗ y) ≫ (t ⊗ s) ◁ (β_ x y).hom ≫
      tensorμ t s y x ≫ (g ⊗ₘ f) =
      (tensorμ s t x y ≫ (f ⊗ₘ g)) ≫ (β_ x' y').hom := by
  rw [← tensorHom_def_assoc, ← interchange_braiding_assoc]
  rw [Category.assoc, BraidedCategory.braiding_naturality]

/-- The original symmetry, applied in both coordinates and passed to the quotient. -/
def braidingIso (X Y : Localization C C) : X ⊗ Y ≅ Y ⊗ X :=
  (ActionLocalization.ofFunctor (C := C)).mapIso
    ((β_ X.obj.1 Y.obj.1).prod (β_ X.obj.2 Y.obj.2))

lemma braidingIso_naturality {X Y X' Y' : Localization C C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom f g ≫ (braidingIso X' Y').hom =
      (braidingIso X Y).hom ≫ tensorHom g f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change ActionLocalization.mkHom (tensorRep f g) ≫ ActionLocalization.ofHom _ =
        ActionLocalization.ofHom _ ≫ ActionLocalization.mkHom (tensorRep g f)
      rw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
      apply Quotient.sound
      refine ⟨β_ f.denom g.denom, ?_⟩
      exact Prod.ext (braiding_coherence f.map.1 g.map.1)
        (braiding_coherence f.map.2 g.map.2)

instance braidedCategory : BraidedCategory (Localization C C) where
  braiding := braidingIso
  braiding_naturality_left f Y := by
    exact braidingIso_naturality f (𝟙 Y)
  braiding_naturality_right X _ _ f := by
    exact braidingIso_naturality (𝟙 X) f
  hexagon_forward X Y Z := by
    change ActionLocalization.ofHom _ ≫ ActionLocalization.ofHom _ ≫
      ActionLocalization.ofHom _ =
      tensorHom (ActionLocalization.ofHom _) (𝟙 Z) ≫ ActionLocalization.ofHom _ ≫
        tensorHom (𝟙 Y) (ActionLocalization.ofHom _)
    rw [← ActionLocalization.ofHom_id Z.obj, ← ActionLocalization.ofHom_id Y.obj,
      tensorHom_ofHom, tensorHom_ofHom, ← ActionLocalization.ofHom_comp,
      ← ActionLocalization.ofHom_comp, ← ActionLocalization.ofHom_comp,
      ← ActionLocalization.ofHom_comp]
    apply congrArg ActionLocalization.ofHom
    apply Prod.ext
    · change (α_ X.obj.1 Y.obj.1 Z.obj.1).hom ≫
        (β_ X.obj.1 (Y.obj.1 ⊗ Z.obj.1)).hom ≫ (α_ Y.obj.1 Z.obj.1 X.obj.1).hom =
        ((β_ X.obj.1 Y.obj.1).hom ⊗ₘ 𝟙 Z.obj.1) ≫ (α_ Y.obj.1 X.obj.1 Z.obj.1).hom ≫
          (𝟙 Y.obj.1 ⊗ₘ (β_ X.obj.1 Z.obj.1).hom)
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        BraidedCategory.hexagon_forward X.obj.1 Y.obj.1 Z.obj.1
    · change (α_ X.obj.2 Y.obj.2 Z.obj.2).hom ≫
        (β_ X.obj.2 (Y.obj.2 ⊗ Z.obj.2)).hom ≫ (α_ Y.obj.2 Z.obj.2 X.obj.2).hom =
        ((β_ X.obj.2 Y.obj.2).hom ⊗ₘ 𝟙 Z.obj.2) ≫ (α_ Y.obj.2 X.obj.2 Z.obj.2).hom ≫
          (𝟙 Y.obj.2 ⊗ₘ (β_ X.obj.2 Z.obj.2).hom)
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        BraidedCategory.hexagon_forward X.obj.2 Y.obj.2 Z.obj.2
  hexagon_reverse X Y Z := by
    change ActionLocalization.ofHom _ ≫ ActionLocalization.ofHom _ ≫
      ActionLocalization.ofHom _ =
      tensorHom (𝟙 X) (ActionLocalization.ofHom _) ≫ ActionLocalization.ofHom _ ≫
        tensorHom (ActionLocalization.ofHom _) (𝟙 Y)
    rw [← ActionLocalization.ofHom_id X.obj, ← ActionLocalization.ofHom_id Y.obj,
      tensorHom_ofHom, tensorHom_ofHom, ← ActionLocalization.ofHom_comp,
      ← ActionLocalization.ofHom_comp, ← ActionLocalization.ofHom_comp,
      ← ActionLocalization.ofHom_comp]
    apply congrArg ActionLocalization.ofHom
    apply Prod.ext
    · change (α_ X.obj.1 Y.obj.1 Z.obj.1).inv ≫
        (β_ (X.obj.1 ⊗ Y.obj.1) Z.obj.1).hom ≫ (α_ Z.obj.1 X.obj.1 Y.obj.1).inv =
        (𝟙 X.obj.1 ⊗ₘ (β_ Y.obj.1 Z.obj.1).hom) ≫ (α_ X.obj.1 Z.obj.1 Y.obj.1).inv ≫
          ((β_ X.obj.1 Z.obj.1).hom ⊗ₘ 𝟙 Y.obj.1)
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        BraidedCategory.hexagon_reverse X.obj.1 Y.obj.1 Z.obj.1
    · change (α_ X.obj.2 Y.obj.2 Z.obj.2).inv ≫
        (β_ (X.obj.2 ⊗ Y.obj.2) Z.obj.2).hom ≫ (α_ Z.obj.2 X.obj.2 Y.obj.2).inv =
        (𝟙 X.obj.2 ⊗ₘ (β_ Y.obj.2 Z.obj.2).hom) ≫ (α_ X.obj.2 Z.obj.2 Y.obj.2).inv ≫
          ((β_ X.obj.2 Z.obj.2).hom ⊗ₘ 𝟙 Y.obj.2)
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        BraidedCategory.hexagon_reverse X.obj.2 Y.obj.2 Z.obj.2

instance symmetricCategory : SymmetricCategory (Localization C C) where
  symmetry X Y := by
    change ActionLocalization.ofHom _ ≫ ActionLocalization.ofHom _ = _
    rw [← ActionLocalization.ofHom_comp]
    exact (congrArg (ActionLocalization.ofHom (C := C))
      (Prod.ext (SymmetricCategory.symmetry X.obj.1 Y.obj.1)
        (SymmetricCategory.symmetry X.obj.2 Y.obj.2))).trans
      (ActionLocalization.ofHom_id (tensorPair X.obj Y.obj))

end CategoryTheory.GroupCompletion.Localization
