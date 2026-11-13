/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmashAdjunction

/-!
# Exponentials pointed by constant maps

For an object under the terminal object, its exponential is pointed
by the transpose of the constant map to the original point.
Precomposition and postcomposition preserve that point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  [CartesianMonoidalCategory C]

/-- The native monoidal product compared with the chosen binary product. -/
abbrev tensorProductIso (X I : C) : X ⊗ I ≅ X ⨯ I :=
  (CartesianMonoidalCategory.tensorLeftIsoProd X).app I

@[reassoc]
theorem tensorProductIso_hom_fst (X I : C) :
    (tensorProductIso X I).hom ≫ prod.fst = CartesianMonoidalCategory.fst X I :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc]
theorem tensorProductIso_hom_snd (X I : C) :
    (tensorProductIso X I).hom ≫ prod.snd = CartesianMonoidalCategory.snd X I :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- The comparison commutes with the actual maps in both factors. -/
@[reassoc]
theorem tensorProductIso_naturality {X Y I K : C} (f : X ⟶ Y) (s : I ⟶ K) :
    (f ⊗ₘ s) ≫ (tensorProductIso Y K).hom =
      (tensorProductIso X I).hom ≫ prod.map f s := by
  apply prod.hom_ext
  · simp only [Category.assoc, tensorProductIso_hom_fst, CartesianMonoidalCategory.tensorHom_fst,
      prod.map_fst, tensorProductIso_hom_fst_assoc]
  · simp only [Category.assoc, tensorProductIso_hom_snd, CartesianMonoidalCategory.tensorHom_snd,
      prod.map_snd, tensorProductIso_hom_snd_assoc]

variable [MonoidalClosed C]

private def tensorLeftIsoRightProduct (I : C) :
    tensorLeft I ≅ prod.functor.flip.obj I :=
  CartesianMonoidalCategory.tensorLeftIsoProd I ≪≫
    NatIso.ofComponents (fun X ↦ prod.braiding I X) (fun f ↦ braid_natural (𝟙 I) f)

/-- Precomposition in the parameter commutes with currying the chosen
right product. -/
theorem prodRightCurry_pre {X Y I K : C} (s : I ⟶ K) (a : X ⨯ K ⟶ Y) :
    (prodRightIhomAdjunction K).homEquiv X Y a ≫ (MonoidalClosed.pre s).app Y =
      (prodRightIhomAdjunction I).homEquiv X Y (prod.map (𝟙 X) s ≫ a) := by
  let e (L : C) : L ⊗ X ≅ X ⨯ L := tensorProductIso L X ≪≫ prod.braiding L X
  have hs : (s ▷ X) ≫ (e K).hom = (e I).hom ≫ prod.map (𝟙 X) s := by
    rw [← tensorHom_id]
    change (s ⊗ₘ 𝟙 X) ≫ (tensorProductIso K X).hom ≫ (prod.braiding K X).hom =
      ((tensorProductIso I X).hom ≫ (prod.braiding I X).hom) ≫ prod.map (𝟙 X) s
    rw [tensorProductIso_naturality_assoc, braid_natural, Category.assoc]
  change ((ihom.adjunction K).ofNatIsoLeft (tensorLeftIsoRightProduct K)).homEquiv X Y a ≫ _ =
    ((ihom.adjunction I).ofNatIsoLeft (tensorLeftIsoRightProduct I)).homEquiv X Y _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change MonoidalClosed.curry ((e K).hom ≫ a) ≫ _ =
    MonoidalClosed.curry ((e I).hom ≫ prod.map (𝟙 X) s ≫ a)
  rw [MonoidalClosed.curry_pre_app, ← Category.assoc, hs, Category.assoc]

namespace Under

variable [HasTerminal C]

/-- The original exponential pointed by the constant map to the target point. -/
def constantPointExponential (I : C) (Y : Under (⊤_ C)) : Under (⊤_ C) :=
  Under.mk ((prodRightIhomAdjunction I).homEquiv (⊤_ C) Y.right
    (terminal.from ((⊤_ C) ⨯ I) ≫ Y.hom))

/-- Restriction in the exponential parameter preserves its constant point. -/
def constantPointExponentialPre {I K : C} (s : I ⟶ K) (Y : Under (⊤_ C)) :
    constantPointExponential K Y ⟶ constantPointExponential I Y :=
  Under.homMk ((MonoidalClosed.pre s).app Y.right) (by
    change (prodRightIhomAdjunction K).homEquiv _ _ _ ≫ _ =
      (prodRightIhomAdjunction I).homEquiv _ _ _
    rw [prodRightCurry_pre]
    exact congrArg ((prodRightIhomAdjunction I).homEquiv (⊤_ C) Y.right)
      (terminal.comp_from_assoc (prod.map (𝟙 (⊤_ C)) s) Y.hom))

/-- The original exponential, pointed by the constant maps, is functorial
in the pointed target. -/
def constantPointExponentialFunctor (I : C) : Under (⊤_ C) ⥤ Under (⊤_ C) where
  obj := constantPointExponential I
  map {Y Z} f := Under.homMk ((ihom I).map f.right) (by
    change (prodRightIhomAdjunction I).homEquiv _ _ _ ≫ _ =
      (prodRightIhomAdjunction I).homEquiv _ _ _
    rw [← (prodRightIhomAdjunction I).homEquiv_naturality_right, Category.assoc, Under.w f])
  map_id _ := Under.UnderMorphism.ext (Functor.map_id _ _)
  map_comp _ _ := Under.UnderMorphism.ext (Functor.map_comp _ _ _)

end Under

end CategoryTheory
