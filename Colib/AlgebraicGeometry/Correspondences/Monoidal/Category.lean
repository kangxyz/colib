/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Exterior
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Symmetric monoidal structure on finite correspondences

The tensor is the existing exterior product of integral correspondences.
The constraints are the graphs of the Cartesian constraints on the smooth
site. Their coherence equations are images of those on the site. The
construction uses interchange, graph product preservation, and the
naturality equations for the exterior product under the constraints.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "Γ" => graphFunctor k
local infixr:70 " ⊠ " => Cor.tensorObj
local infixr:70 " ⊠ₘ " => exteriorProduct

/-- Interchange for the exterior product of arbitrary correspondences. -/
def ExteriorInterchange (k : Type u) [Field k] : Prop :=
  ∀ {X X' X'' Y Y' Y'' : Cor k}
    (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'') (g' : Y' ⟶ Y''),
    (f ⊠ₘ g) ≫ (f' ⊠ₘ g') = (f ≫ f') ⊠ₘ (g ≫ g')

/-- The exterior product of ordinary graph maps is the graph of the literal product map. -/
def ExteriorGraphProduct (k : Type u) [Field k] : Prop :=
  ∀ {X X' Y Y' : SmoothSite (Spec (.of k))} (f : X ⟶ X') (g : Y ⟶ Y'),
    (graphFunctor k).map f ⊠ₘ (graphFunctor k).map g =
      (graphFunctor k).map (SmoothSite.productMap f g)

/-- The monoidal unit is the base smooth scheme. -/
def tensorUnit (k : Type u) [Field k] : Cor k :=
  (graphFunctor k).obj (𝟙_ (SmoothSite (Spec (.of k))))

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- The associator is the graph of the associator of literal products. -/
def tensorAssociator (X Y Z : Cor k) : ((X ⊠ Y) ⊠ Z) ≅ X ⊠ (Y ⊠ Z) :=
  (Γ).mapIso (α_ X.toSmoothSite Y.toSmoothSite Z.toSmoothSite)

/-- The left unitor is the graph of the left unitor of literal products. -/
def tensorLeftUnitor (X : Cor k) : (tensorUnit k ⊠ X) ≅ X :=
  (Γ).mapIso (λ_ X.toSmoothSite)

/-- The right unitor is the graph of the right unitor of literal products. -/
def tensorRightUnitor (X : Cor k) : (X ⊠ tensorUnit k) ≅ X :=
  (Γ).mapIso (ρ_ X.toSmoothSite)

/-- The braiding is the graph of the switch of factors. -/
def tensorBraiding (X Y : Cor k) : (X ⊠ Y) ≅ Y ⊠ X :=
  (Γ).mapIso (β_ X.toSmoothSite Y.toSmoothSite)

/-- Associator naturality for the signed exterior product. -/
def ExteriorAssociatorNaturality (k : Type u) [Field k] : Prop :=
  ∀ {X X' Y Y' Z Z' : Cor k} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    ((f ⊠ₘ g) ⊠ₘ h) ≫ (tensorAssociator X' Y' Z').hom =
      (tensorAssociator X Y Z).hom ≫ (f ⊠ₘ (g ⊠ₘ h))

/-- Right unitor naturality for the signed exterior product. -/
def ExteriorRightUnitorNaturality (k : Type u) [Field k] : Prop :=
  ∀ {X Y : Cor k} (f : X ⟶ Y),
    (f ⊠ₘ 𝟙 (tensorUnit k)) ≫ (tensorRightUnitor Y).hom = (tensorRightUnitor X).hom ≫ f

/-- Switch naturality for the signed exterior product. -/
def ExteriorBraidingNaturality (k : Type u) [Field k] : Prop :=
  ∀ {X X' Y Y' : Cor k} (f : X ⟶ X') (g : Y ⟶ Y'),
    (f ⊠ₘ g) ≫ (tensorBraiding X' Y').hom = (tensorBraiding X Y).hom ≫ (g ⊠ₘ f)

private theorem exteriorGraphTensor (hG : ExteriorGraphProduct k)
    {X X' Y Y' : Sm} (f : X ⟶ X') (g : Y ⟶ Y') :
    (Γ).map f ⊠ₘ (Γ).map g = (Γ).map (f ⊗ₘ g) := by
  rw [SmoothSite.tensorHom_eq_productMap]
  exact hG f g

/-- The exterior product of identities is the identity. -/
theorem exterior_id (hG : ExteriorGraphProduct k) (X Y : Cor k) :
    𝟙 X ⊠ₘ 𝟙 Y = 𝟙 (X ⊠ Y) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  change (Γ).map (𝟙 X) ⊠ₘ (Γ).map (𝟙 Y) = 𝟙 ((Γ).obj (X ⊗ Y))
  calc
    _ = (Γ).map (𝟙 X ⊗ₘ 𝟙 Y) := exteriorGraphTensor hG _ _
    _ = _ := by
      rw [id_tensorHom_id]
      exact (Γ).map_id (X ⊗ Y)

private theorem tensorLeftUnitor_factor (X : Cor k) :
    (tensorBraiding (tensorUnit k) X).hom ≫ (tensorRightUnitor X).hom =
      (tensorLeftUnitor X).hom := by
  change (Γ).map (β_ (𝟙_ Sm) X.toSmoothSite).hom ≫
    (Γ).map (ρ_ X.toSmoothSite).hom = (Γ).map (λ_ X.toSmoothSite).hom
  rw [← Functor.map_comp, braiding_rightUnitor]

/-- Left unit naturality follows from switch and right unit naturality. -/
theorem exteriorLeftUnitorNaturality (hR : ExteriorRightUnitorNaturality k)
    (hB : ExteriorBraidingNaturality k) {X Y : Cor k} (f : X ⟶ Y) :
    (𝟙 (tensorUnit k) ⊠ₘ f) ≫ (tensorLeftUnitor Y).hom =
      (tensorLeftUnitor X).hom ≫ f := by
  rw [← tensorLeftUnitor_factor Y, ← tensorLeftUnitor_factor X, ← Category.assoc,
    hB (𝟙 (tensorUnit k)) f, Category.assoc, hR f, Category.assoc]

/-- The graph associator satisfies the pentagon. -/
theorem tensorPentagon (hG : ExteriorGraphProduct k) (W X Y Z : Cor k) :
    ((tensorAssociator W X Y).hom ⊠ₘ 𝟙 Z) ≫ (tensorAssociator W (X ⊠ Y) Z).hom ≫
        (𝟙 W ⊠ₘ (tensorAssociator X Y Z).hom) =
      (tensorAssociator (W ⊠ X) Y Z).hom ≫ (tensorAssociator W X (Y ⊠ Z)).hom := by
  obtain ⟨W⟩ := W
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨Z⟩ := Z
  change ((Γ).map (α_ W X Y).hom ⊠ₘ (Γ).map (𝟙 Z)) ≫
        (Γ).map (α_ W (X ⊗ Y) Z).hom ≫ ((Γ).map (𝟙 W) ⊠ₘ (Γ).map (α_ X Y Z).hom) =
      (Γ).map (α_ (W ⊗ X) Y Z).hom ≫ (Γ).map (α_ W X (Y ⊗ Z)).hom
  let f₁ : ((W ⊗ X) ⊗ Y) ⊗ Z ⟶ (W ⊗ (X ⊗ Y)) ⊗ Z :=
    (α_ W X Y).hom ▷ Z
  let f₂ : (W ⊗ (X ⊗ Y)) ⊗ Z ⟶ W ⊗ ((X ⊗ Y) ⊗ Z) :=
    (α_ W (X ⊗ Y) Z).hom
  let f₃ : W ⊗ ((X ⊗ Y) ⊗ Z) ⟶ W ⊗ (X ⊗ (Y ⊗ Z)) :=
    W ◁ (α_ X Y Z).hom
  have h₁ : ((Γ).map (α_ W X Y).hom ⊠ₘ (Γ).map (𝟙 Z)) = (Γ).map f₁ :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (tensorHom_id _ _))
  have h₃ : ((Γ).map (𝟙 W) ⊠ₘ (Γ).map (α_ X Y Z).hom) = (Γ).map f₃ :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (id_tensorHom _ _))
  calc
    _ = (Γ).map f₁ ≫ (Γ).map f₂ ≫ (Γ).map f₃ :=
      congrArg₂ (fun a c => a ≫ (Γ).map f₂ ≫ c) h₁ h₃
    _ = (Γ).map (f₁ ≫ f₂ ≫ f₃) :=
      (Functor.map_comp_assoc (Γ) f₁ f₂ ((Γ).map f₃)).symm.trans
        (by rw [← Functor.map_comp, Category.assoc])
    _ = (Γ).map ((α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) :=
      congrArg ((Γ).map) (pentagon W X Y Z)
    _ = _ := (Γ).map_comp _ _

/-- The graph associator and unitors satisfy the triangle. -/
theorem tensorTriangle (hG : ExteriorGraphProduct k) (X Y : Cor k) :
    (tensorAssociator X (tensorUnit k) Y).hom ≫ (𝟙 X ⊠ₘ (tensorLeftUnitor Y).hom) =
      (tensorRightUnitor X).hom ⊠ₘ 𝟙 Y := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  change (Γ).map (α_ X (𝟙_ Sm) Y).hom ≫ ((Γ).map (𝟙 X) ⊠ₘ (Γ).map (λ_ Y).hom) =
    (Γ).map (ρ_ X).hom ⊠ₘ (Γ).map (𝟙 Y)
  have h₁ : ((Γ).map (𝟙 X) ⊠ₘ (Γ).map (λ_ Y).hom) = (Γ).map (X ◁ (λ_ Y).hom) :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (id_tensorHom _ _))
  have h₂ : ((Γ).map (ρ_ X).hom ⊠ₘ (Γ).map (𝟙 Y)) = (Γ).map ((ρ_ X).hom ▷ Y) :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (tensorHom_id _ _))
  calc
    _ = (Γ).map (α_ X (𝟙_ Sm) Y).hom ≫ (Γ).map (X ◁ (λ_ Y).hom) :=
      congrArg ((Γ).map (α_ X (𝟙_ Sm) Y).hom ≫ ·) h₁
    _ = (Γ).map ((α_ X (𝟙_ Sm) Y).hom ≫ X ◁ (λ_ Y).hom) := ((Γ).map_comp _ _).symm
    _ = (Γ).map ((ρ_ X).hom ▷ Y) := congrArg ((Γ).map) (triangle X Y)
    _ = _ := h₂.symm

/-- The Cartesian objects and graph constraints with the native exterior product on arrows. -/
@[instance_reducible]
def exteriorMonoidalCategoryStruct (k : Type u) [Field k] : MonoidalCategoryStruct (Cor k) where
  tensorObj := Cor.tensorObj
  tensorHom := fun f g => exteriorProduct f g
  whiskerLeft X _ _ f := 𝟙 X ⊠ₘ f
  whiskerRight f Y := f ⊠ₘ 𝟙 Y
  tensorUnit := tensorUnit k
  associator := tensorAssociator
  leftUnitor := tensorLeftUnitor
  rightUnitor := tensorRightUnitor

/-- The monoidal structure induced by the exterior product equations. -/
@[instance_reducible]
def exteriorMonoidalCategory (hI : ExteriorInterchange k) (hG : ExteriorGraphProduct k)
    (hA : ExteriorAssociatorNaturality k) (hR : ExteriorRightUnitorNaturality k)
    (hB : ExteriorBraidingNaturality k) : MonoidalCategory (Cor k) :=
  letI := exteriorMonoidalCategoryStruct k
  MonoidalCategory.ofTensorHom (exterior_id hG) (by intros; rfl) (by intros; rfl)
    (fun f g f' g' => hI f g f' g') (fun f g h => hA f g h)
    (exteriorLeftUnitorNaturality hR hB) (fun f => hR f) (tensorPentagon hG) (tensorTriangle hG)

/-- The graph associator and factor switch satisfy the first hexagon. -/
theorem tensorHexagonForward (hG : ExteriorGraphProduct k) (X Y Z : Cor k) :
    (tensorAssociator X Y Z).hom ≫ (tensorBraiding X (Y ⊠ Z)).hom ≫
        (tensorAssociator Y Z X).hom =
      ((tensorBraiding X Y).hom ⊠ₘ 𝟙 Z) ≫ (tensorAssociator Y X Z).hom ≫
        (𝟙 Y ⊠ₘ (tensorBraiding X Z).hom) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨Z⟩ := Z
  change (Γ).map (α_ X Y Z).hom ≫ (Γ).map (β_ X (Y ⊗ Z)).hom ≫ (Γ).map (α_ Y Z X).hom =
    ((Γ).map (β_ X Y).hom ⊠ₘ (Γ).map (𝟙 Z)) ≫ (Γ).map (α_ Y X Z).hom ≫
      ((Γ).map (𝟙 Y) ⊠ₘ (Γ).map (β_ X Z).hom)
  have h₁ : ((Γ).map (β_ X Y).hom ⊠ₘ (Γ).map (𝟙 Z)) = (Γ).map ((β_ X Y).hom ▷ Z) :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (tensorHom_id _ _))
  have h₃ : ((Γ).map (𝟙 Y) ⊠ₘ (Γ).map (β_ X Z).hom) = (Γ).map (Y ◁ (β_ X Z).hom) :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (id_tensorHom _ _))
  calc
    _ = (Γ).map ((α_ X Y Z).hom ≫ (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom) := by
      simp only [← Functor.map_comp]
    _ = (Γ).map (((β_ X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom) :=
      congrArg ((Γ).map) (hexagon_forward X Y Z)
    _ = (Γ).map ((β_ X Y).hom ▷ Z) ≫
        (Γ).map (α_ Y X Z).hom ≫ (Γ).map (Y ◁ (β_ X Z).hom) := by
      rw [Functor.map_comp, Functor.map_comp]
    _ = _ := congrArg₂ (fun a c => a ≫ (Γ).map (α_ Y X Z).hom ≫ c) h₁.symm h₃.symm

/-- The graph associator and factor switch satisfy the second hexagon. -/
theorem tensorHexagonReverse (hG : ExteriorGraphProduct k) (X Y Z : Cor k) :
    (tensorAssociator X Y Z).inv ≫ (tensorBraiding (X ⊠ Y) Z).hom ≫
        (tensorAssociator Z X Y).inv =
      (𝟙 X ⊠ₘ (tensorBraiding Y Z).hom) ≫ (tensorAssociator X Z Y).inv ≫
        ((tensorBraiding X Z).hom ⊠ₘ 𝟙 Y) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨Z⟩ := Z
  change (Γ).map (α_ X Y Z).inv ≫ (Γ).map (β_ (X ⊗ Y) Z).hom ≫ (Γ).map (α_ Z X Y).inv =
    ((Γ).map (𝟙 X) ⊠ₘ (Γ).map (β_ Y Z).hom) ≫ (Γ).map (α_ X Z Y).inv ≫
      ((Γ).map (β_ X Z).hom ⊠ₘ (Γ).map (𝟙 Y))
  have h₁ : ((Γ).map (𝟙 X) ⊠ₘ (Γ).map (β_ Y Z).hom) = (Γ).map (X ◁ (β_ Y Z).hom) :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (id_tensorHom _ _))
  have h₃ : ((Γ).map (β_ X Z).hom ⊠ₘ (Γ).map (𝟙 Y)) = (Γ).map ((β_ X Z).hom ▷ Y) :=
    (exteriorGraphTensor hG _ _).trans (congrArg ((Γ).map) (tensorHom_id _ _))
  calc
    _ = (Γ).map ((α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) := by
      simp only [← Functor.map_comp]
    _ = (Γ).map ((X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y) :=
      congrArg ((Γ).map) (hexagon_reverse X Y Z)
    _ = (Γ).map (X ◁ (β_ Y Z).hom) ≫
        (Γ).map (α_ X Z Y).inv ≫ (Γ).map ((β_ X Z).hom ▷ Y) := by
      rw [Functor.map_comp, Functor.map_comp]
    _ = _ := congrArg₂ (fun a c => a ≫ (Γ).map (α_ X Z Y).inv ≫ c) h₁.symm h₃.symm

/-- The factor switch gives the symmetric structure on finite correspondences. -/
@[instance_reducible]
def exteriorSymmetricCategory (hI : ExteriorInterchange k) (hG : ExteriorGraphProduct k)
    (hA : ExteriorAssociatorNaturality k) (hR : ExteriorRightUnitorNaturality k)
    (hB : ExteriorBraidingNaturality k) :
    letI := exteriorMonoidalCategory hI hG hA hR hB
    SymmetricCategory (Cor k) :=
  letI := exteriorMonoidalCategory hI hG hA hR hB
  { braiding := tensorBraiding
    braiding_naturality_right := fun X _ _ f => hB (𝟙 X) f
    braiding_naturality_left := fun f Y => hB f (𝟙 Y)
    hexagon_forward := tensorHexagonForward hG
    hexagon_reverse := tensorHexagonReverse hG
    symmetry X Y := by
      change (Γ).map (β_ X.toSmoothSite Y.toSmoothSite).hom ≫
        (Γ).map (β_ Y.toSmoothSite X.toSmoothSite).hom =
          𝟙 ((Γ).obj (X.toSmoothSite ⊗ Y.toSmoothSite))
      rw [← Functor.map_comp, SymmetricCategory.symmetry]
      exact (Γ).map_id (X.toSmoothSite ⊗ Y.toSmoothSite) }

/-- The exterior product is additive in both variables. -/
theorem exteriorMonoidalPreadditive (hI : ExteriorInterchange k) (hG : ExteriorGraphProduct k)
    (hA : ExteriorAssociatorNaturality k) (hR : ExteriorRightUnitorNaturality k)
    (hB : ExteriorBraidingNaturality k) :
    letI := exteriorMonoidalCategory hI hG hA hR hB
    MonoidalPreadditive (Cor k) :=
  letI := exteriorMonoidalCategory hI hG hA hR hB
  { whiskerLeft_zero := fun {X _ _} => exteriorProduct_zero_right (𝟙 X)
    zero_whiskerRight := fun {X _ _} => exteriorProduct_zero_left (𝟙 X)
    whiskerLeft_add := fun {X _ _} f g => exteriorProduct_add_right (𝟙 X) f g
    add_whiskerRight := fun {X _ _} f g => exteriorProduct_add_left f g (𝟙 X) }

/-- The graph functor has identity unit and tensor comparison isomorphisms. -/
def graphCoreMonoidal (hI : ExteriorInterchange k) (hG : ExteriorGraphProduct k)
    (hA : ExteriorAssociatorNaturality k) (hR : ExteriorRightUnitorNaturality k)
    (hB : ExteriorBraidingNaturality k) :
    letI := exteriorMonoidalCategory hI hG hA hR hB
    (Γ).CoreMonoidal :=
  letI := exteriorMonoidalCategory hI hG hA hR hB
  { εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by
      intro X Y f Z
      change ((Γ).map f ⊠ₘ (Γ).map (𝟙 Z)) ≫ 𝟙 _ = 𝟙 _ ≫ (Γ).map (f ▷ Z)
      rw [Category.comp_id, Category.id_comp, exteriorGraphTensor hG, tensorHom_id]
    μIso_hom_natural_right := by
      intro X Y Z f
      change ((Γ).map (𝟙 Z) ⊠ₘ (Γ).map f) ≫ 𝟙 _ = 𝟙 _ ≫ (Γ).map (Z ◁ f)
      rw [Category.comp_id, Category.id_comp, exteriorGraphTensor hG, id_tensorHom]
    associativity := by
      intro X Y Z
      change (𝟙 ((Γ).obj (X ⊗ Y)) ⊠ₘ 𝟙 ((Γ).obj Z)) ≫ 𝟙 _ ≫
          (Γ).map (α_ X Y Z).hom =
        (Γ).map (α_ X Y Z).hom ≫ (𝟙 ((Γ).obj X) ⊠ₘ 𝟙 ((Γ).obj (Y ⊗ Z))) ≫ 𝟙 _
      let a : (Γ).obj ((X ⊗ Y) ⊗ Z) ⟶ (Γ).obj (X ⊗ (Y ⊗ Z)) :=
        (Γ).map (α_ X Y Z).hom
      let p : (Γ).obj ((X ⊗ Y) ⊗ Z) ⟶ (Γ).obj ((X ⊗ Y) ⊗ Z) :=
        𝟙 ((Γ).obj (X ⊗ Y)) ⊠ₘ 𝟙 ((Γ).obj Z)
      let q : (Γ).obj (X ⊗ (Y ⊗ Z)) ⟶ (Γ).obj (X ⊗ (Y ⊗ Z)) :=
        𝟙 ((Γ).obj X) ⊠ₘ 𝟙 ((Γ).obj (Y ⊗ Z))
      have hp : p = 𝟙 _ := exterior_id hG ((Γ).obj (X ⊗ Y)) ((Γ).obj Z)
      have hq : q = 𝟙 _ := exterior_id hG ((Γ).obj X) ((Γ).obj (Y ⊗ Z))
      change p ≫ 𝟙 _ ≫ a = a ≫ q ≫ 𝟙 _
      rw [hp, hq]
      simp only [Category.id_comp, Category.comp_id]
    left_unitality := by
      intro X
      change (Γ).map (λ_ X).hom =
        (𝟙 ((Γ).obj (𝟙_ Sm)) ⊠ₘ 𝟙 ((Γ).obj X)) ≫ 𝟙 _ ≫ (Γ).map (λ_ X).hom
      simp only [exterior_id hG, Category.id_comp]
    right_unitality := by
      intro X
      change (Γ).map (ρ_ X).hom =
        (𝟙 ((Γ).obj X) ⊠ₘ 𝟙 ((Γ).obj (𝟙_ Sm))) ≫ 𝟙 _ ≫ (Γ).map (ρ_ X).hom
      simp only [exterior_id hG, Category.id_comp] }

/-- The ordinary graph functor is braided with identity unit and tensor comparisons. -/
@[instance_reducible]
def exteriorGraphBraided (hI : ExteriorInterchange k) (hG : ExteriorGraphProduct k)
    (hA : ExteriorAssociatorNaturality k) (hR : ExteriorRightUnitorNaturality k)
    (hB : ExteriorBraidingNaturality k) :
    letI := exteriorMonoidalCategory hI hG hA hR hB
    letI := exteriorSymmetricCategory hI hG hA hR hB
    (Γ).Braided :=
  letI := exteriorMonoidalCategory hI hG hA hR hB
  letI := exteriorSymmetricCategory hI hG hA hR hB
  { toMonoidal := (graphCoreMonoidal hI hG hA hR hB).toMonoidal
    braided X Y := by
      change 𝟙 _ ≫ (Γ).map (β_ X Y).hom = (Γ).map (β_ X Y).hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id] }

end AlgebraicGeometry.Cor
