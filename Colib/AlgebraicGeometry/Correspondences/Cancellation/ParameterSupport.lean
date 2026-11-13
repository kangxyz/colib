/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Extension of a support by an external parameter

Extending a finite support by a smooth parameter keeps the actual projection
to the old source, the external parameter and the old factor. Finiteness and
closed immersion are inherited from the original support map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {X T : SmoothSite S} {P : Scheme.{u}}
  (g : P ⟶ (product X T).left) (U : SmoothSite S)

local notation "A" => (product X T)
local notation "D" => (product (product X U) T)
set_option quotPrecheck false in
local notation "b" => (g ≫ (A).hom)

/-- The actual base extension of the support, with the new parameter next to
its base and the old factor in the last position. -/
def supportParameterExtension : pullback b U.hom ⟶ (D).left :=
  pullbackParameterExtensionMap g (A).hom U.hom ≫ (productSwapLast X T U).left

/-- Base change and the factor permutation preserve the specified morphism property. -/
theorem supportParameterExtension_of_property (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] [Q.RespectsIso] (hg : Q g) :
    Q (supportParameterExtension g U) := by
  let e := (forgetScheme S).mapIso (productSwapLastIso X T U)
  let : IsIso (productSwapLast X T U).left := inferInstanceAs (IsIso e.hom)
  rw [supportParameterExtension, MorphismProperty.cancel_right_of_respectsIso (P := Q)]
  exact MorphismProperty.of_isPullback
    (pullbackParameterExtension_isPullback g (A).hom U.hom).flip hg

instance supportParameterExtension_isFinite [IsFinite g] :
    IsFinite (supportParameterExtension g U) :=
  supportParameterExtension_of_property g U (@IsFinite.{u}) inferInstance

instance supportParameterExtension_isClosedImmersion [IsClosedImmersion g] :
    IsClosedImmersion (supportParameterExtension g U) :=
  supportParameterExtension_of_property g U (@IsClosedImmersion.{u}) inferInstance

/-- The original source base map is unchanged by the extension. -/
@[reassoc] theorem supportParameterExtension_base :
    supportParameterExtension g U ≫ (productFst (product X U) T).left ≫
      (productFst X U).left = pullback.fst b U.hom ≫ g ≫ (productFst X T).left := by
  have h : productSwapLast X T U ≫ productFst (product X U) T ≫ productFst X U =
      productFst A U ≫ productFst X T := by simp [productSwapLast]
  have hl := congrArg (fun φ => φ.left) h
  change (productSwapLast X T U).left ≫ (productFst (product X U) T).left ≫
    (productFst X U).left = (productFst A U).left ≫ (productFst X T).left at hl
  have h₁ : pullbackParameterExtensionMap g (A).hom U.hom ≫ (productFst A U).left =
      pullback.fst b U.hom ≫ g :=
    pullbackParameterExtensionMap_fst g (A).hom U.hom
  rw [supportParameterExtension, Category.assoc, hl, ← Category.assoc, h₁, Category.assoc]

/-- The structural map of the extended support is its original structural map. -/
@[reassoc] theorem supportParameterExtension_over :
    supportParameterExtension g U ≫ (productFst (product X U) T).left ≫
      (product X U).hom = pullback.fst b U.hom ≫ b := by
  change supportParameterExtension g U ≫ (productFst (product X U) T).left ≫
      (productFst X U).left ≫ X.hom = pullback.fst b U.hom ≫ g ≫ (productFst X T).left ≫ X.hom
  exact supportParameterExtension_base_assoc g U X.hom

/-- The new parameter is the second projection of the support product. -/
@[reassoc] theorem supportParameterExtension_parameter :
    supportParameterExtension g U ≫ (productFst (product X U) T).left ≫
      (productSnd X U).left = pullback.snd b U.hom := by
  have h : productSwapLast X T U ≫ productFst (product X U) T ≫ productSnd X U =
      productSnd A U := by simp [productSwapLast]
  have hl := congrArg (fun φ => φ.left) h
  change (productSwapLast X T U).left ≫ (productFst (product X U) T).left ≫
    (productSnd X U).left = (productSnd A U).left at hl
  rw [supportParameterExtension, Category.assoc, hl]
  exact pullbackParameterExtensionMap_snd g (A).hom U.hom

/-- The last factor remains the original factor. -/
@[reassoc] theorem supportParameterExtension_oldFactor :
    supportParameterExtension g U ≫ (productSnd (product X U) T).left =
      pullback.fst b U.hom ≫ g ≫ (productSnd X T).left := by
  have hl := congrArg (fun φ => φ.left) (productSwapLast_snd X T U)
  change (productSwapLast X T U).left ≫ (productSnd (product X U) T).left =
    (productFst A U).left ≫ (productSnd X T).left at hl
  have h₁ : pullbackParameterExtensionMap g (A).hom U.hom ≫ (productFst A U).left =
      pullback.fst b U.hom ≫ g :=
    pullbackParameterExtensionMap_fst g (A).hom U.hom
  rw [supportParameterExtension, Category.assoc, hl, ← Category.assoc, h₁, Category.assoc]

/-- A parameter with irreducible geometric fibres carries a component support
to the corresponding component of the extended source. -/
theorem supportParameterExtension_range_mem_irreducibleComponents
    [GeometricallyIrreducible U.hom] (hg : Set.range g ∈ irreducibleComponents (A).left) :
    Set.range (supportParameterExtension g U) ∈ irreducibleComponents (D).left := by
  let t := pullbackParameterExtensionMap g (A).hom U.hom
  let π := pullback.fst (A).hom U.hom
  have h := pullbackParameterExtension_isPullback g (A).hom U.hom
  have hr : Set.range t = π ⁻¹' Set.range g := by
    calc
      _ = Set.range (pullback.fst π g) :=
        range_eq_range_of_surjective t _ h.isoPullback.hom h.isoPullback_hom_fst
      _ = _ := Scheme.Pullback.range_fst π g
  have hC : Set.range t ∈ irreducibleComponents (product A U).left := by
    rw [hr]
    exact ((π.irreducibleComponentsEquiv π.isOpenMap).symm ⟨Set.range g, hg⟩).property
  let e := (forgetScheme S).mapIso (productSwapLastIso X T U)
  have hne : (Set.range t ∩ Set.range e.inv).Nonempty := by
    rw [Set.range_eq_univ.mpr e.inv.surjective, Set.inter_univ]
    exact hC.1.nonempty
  have hpre := preimage_mem_irreducibleComponents hC e.inv.isOpenEmbedding hne
  have himage : e.hom '' Set.range t = e.inv ⁻¹' Set.range t :=
    (Scheme.homeoOfIso e).image_eq_preimage_symm _
  change Set.range (⇑e.hom ∘ ⇑t) ∈ irreducibleComponents (D).left
  rwa [Set.range_comp, himage]

end AlgebraicGeometry.Scheme.SmoothSite
