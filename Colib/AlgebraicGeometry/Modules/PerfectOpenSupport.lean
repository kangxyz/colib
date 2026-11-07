/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupport

/-! # Exact identification of native relative-acyclic and supported complexes

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/OpenSupport.lean:54-189
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Cofibrations are ambient Mono
on both sides. Objects, maps and inclusion composites remain literal.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open Waldhausen Fibration
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- Forget the redundant nested full-subcategory wrapper. -/
def perfectAcyclicToSupported :
    AcyclicCategory (perfectOpenNested j) ⥤ (perfectSupported j).FullSubcategory where
  obj K := ⟨K.obj.obj, K.obj.property, (perfectOpenAcyclic_iff j K.obj).1 K.property⟩
  map f := (perfectSupported j).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def perfectSupportedToAcyclic :
    (perfectSupported j).FullSubcategory ⥤ AcyclicCategory (perfectOpenNested j) where
  obj K := ⟨⟨K.obj, K.property.1⟩,
    (perfectOpenAcyclic_iff j ⟨K.obj, K.property.1⟩).2 K.property.2⟩
  map f := (acyclicObjects (perfectOpenNested j)).homMk
    ((RingedSpace.IsPerfectComplex (X := X.toRingedSpace)).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem perfectAcyclicToSupported_obj
    (K : AcyclicCategory (perfectOpenNested j)) :
    ((perfectAcyclicToSupported j).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem perfectAcyclicToSupported_map
    {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L) :
    ((perfectAcyclicToSupported j).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem perfectSupportedToAcyclic_obj
    (K : (perfectSupported j).FullSubcategory) :
    ((perfectSupportedToAcyclic j).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem perfectSupportedToAcyclic_map
    {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    ((perfectSupportedToAcyclic j).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem perfectAcyclicToSupported_comp_inverse :
    perfectAcyclicToSupported j ⋙ perfectSupportedToAcyclic j =
      𝟭 (AcyclicCategory (perfectOpenNested j)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem perfectSupportedToAcyclic_comp_inverse :
    perfectSupportedToAcyclic j ⋙ perfectAcyclicToSupported j =
      𝟭 ((perfectSupported j).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem perfectAcyclicToSupported_comp_inclusion :
    perfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
      (show perfectSupported j ≤ RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
        from fun _ h ↦ h.1) =
      acyclicInclusion (perfectOpenNested j) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem perfectSupportedToAcyclic_comp_inclusion :
    perfectSupportedToAcyclic j ⋙ acyclicInclusion (perfectOpenNested j) =
      ObjectProperty.ιOfLE
        (show perfectSupported j ≤ RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
        from fun _ h ↦ h.1) := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
def perfectAcyclicSupportedEquivalence :
    AcyclicCategory (perfectOpenNested j) ≌ (perfectSupported j).FullSubcategory where
  functor := perfectAcyclicToSupported j
  inverse := perfectSupportedToAcyclic j
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (perfectAcyclicToSupported j).IsEquivalence :=
  (perfectAcyclicSupportedEquivalence j).isEquivalence_functor
local instance : (perfectSupportedToAcyclic j).IsEquivalence :=
  (perfectAcyclicSupportedEquivalence j).isEquivalence_inverse

/-- Flattening is exact for the original inherited fine weak equivalences. -/
theorem perfectAcyclicToSupported_exact :
    IsExact (acyclicStructure (perfectOpenNested j)).cof
      (acyclicStructure (perfectOpenNested j)).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectAcyclicToSupported j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (perfectSupportedToAcyclic j) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (perfectAcyclicToSupported j)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
theorem perfectSupportedToAcyclic_exact :
    IsExact (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (acyclicStructure (perfectOpenNested j)).cof
      (acyclicStructure (perfectOpenNested j)).weq
      (perfectSupportedToAcyclic j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (perfectAcyclicToSupported j) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (perfectSupportedToAcyclic j)

/-- The actual supported inclusion is preserved at the functor level. -/
def perfectAcyclicToSupportedInclusionIso :
    perfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
      (show perfectSupported j ≤ RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
        from fun _ h ↦ h.1) ≅
      acyclicInclusion (perfectOpenNested j) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

end AlgebraicGeometry.Scheme.Modules
