/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenFibration
public import Colib.AlgebraicGeometry.Modules.PerfectSupportUnion

/-!
# Literal flattening of the supported relative fiber

The relative acyclic category is exactly the category of native perfect complexes
supported outside the union of the auxiliary open and the image of the immersion.
The equivalence preserves actual complexes, chain maps and supported inclusion.
Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Support.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Ambient monomorphisms replace the old
exact-subcategory cofibration presentation; no fine-open comparison is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Relative coarse acyclicity is the actual support predicate, in every degree. -/
theorem perfectSupportedOpenAcyclic_iff (K : (perfectSupported T.ι).FullSubcategory) :
    Acyclic (perfectSupportedOpenWeakWaldhausen j T) K ↔
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).Acyclic := by
  have hZ : IsZero (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (perfectSupportedWaldhausen T.ι).zero.obj) :=
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      ((perfectSupported T.ι).ι.map_isZero (perfectSupportedWaldhausen T.ι).isZero)
  change QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((perfectSupportedWaldhausen T.ι).isZero.to_ K).hom) ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Forget the redundant nested full-subcategory wrapper. -/
def perfectSupportedOpenAcyclicToSupported :
    AcyclicCategory (perfectSupportedOpenNested j T) ⥤ (perfectSupported (T ⊔
      j.opensRange).ι).FullSubcategory where
  obj K := ⟨K.obj.obj, (perfectSupported_sup_opensRange_iff j T K.obj.obj).mpr
    ⟨K.obj.property, (perfectSupportedOpenAcyclic_iff j T K.obj).1 K.property⟩⟩
  map f := (perfectSupported (T ⊔ j.opensRange).ι).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def perfectSupportedUnionToAcyclic :
    (perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory ⥤ AcyclicCategory
      (perfectSupportedOpenNested j T) where
  obj K := ⟨⟨K.obj, ((perfectSupported_sup_opensRange_iff j T K.obj).mp K.property).1⟩,
    (perfectSupportedOpenAcyclic_iff j T _).2
      ((perfectSupported_sup_opensRange_iff j T K.obj).mp K.property).2⟩
  map f := (acyclicObjects (perfectSupportedOpenNested j T)).homMk ((perfectSupported T.ι).homMk
    f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem perfectSupportedOpenAcyclicToSupported_obj
    (K : AcyclicCategory (perfectSupportedOpenNested j T)) :
    ((perfectSupportedOpenAcyclicToSupported j T).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem perfectSupportedOpenAcyclicToSupported_map
    {K L : AcyclicCategory (perfectSupportedOpenNested j T)} (f : K ⟶ L) :
    ((perfectSupportedOpenAcyclicToSupported j T).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem perfectSupportedUnionToAcyclic_obj
    (K : (perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) :
    ((perfectSupportedUnionToAcyclic j T).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem perfectSupportedUnionToAcyclic_map
    {K L : (perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory} (f : K ⟶ L) :
    ((perfectSupportedUnionToAcyclic j T).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem perfectSupportedOpenAcyclicToSupported_comp_inverse :
    perfectSupportedOpenAcyclicToSupported j T ⋙ perfectSupportedUnionToAcyclic j T =
      𝟭 (AcyclicCategory (perfectSupportedOpenNested j T)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem perfectSupportedUnionToAcyclic_comp_inverse :
    perfectSupportedUnionToAcyclic j T ⋙ perfectSupportedOpenAcyclicToSupported j T =
      𝟭 ((perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem perfectSupportedOpenAcyclicToSupported_comp_inclusion :
    perfectSupportedOpenAcyclicToSupported j T ⋙ ObjectProperty.ιOfLE
      (show perfectSupported (T ⊔ j.opensRange).ι ≤ perfectSupported T.ι from fun K h ↦
        ((perfectSupported_sup_opensRange_iff j T K).mp h).1) =
      acyclicInclusion (perfectSupportedOpenNested j T) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem perfectSupportedUnionToAcyclic_comp_inclusion :
    perfectSupportedUnionToAcyclic j T ⋙ acyclicInclusion (perfectSupportedOpenNested j T) =
      ObjectProperty.ιOfLE
        (show perfectSupported (T ⊔ j.opensRange).ι ≤ perfectSupported T.ι from fun K h ↦
          ((perfectSupported_sup_opensRange_iff j T K).mp h).1) := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
def perfectSupportedOpenAcyclicSupportedEquivalence :
    AcyclicCategory (perfectSupportedOpenNested j T) ≌ (perfectSupported (T ⊔
      j.opensRange).ι).FullSubcategory where
  functor := perfectSupportedOpenAcyclicToSupported j T
  inverse := perfectSupportedUnionToAcyclic j T
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (perfectSupportedOpenAcyclicToSupported j T).IsEquivalence :=
  (perfectSupportedOpenAcyclicSupportedEquivalence j T).isEquivalence_functor
local instance : (perfectSupportedUnionToAcyclic j T).IsEquivalence :=
  (perfectSupportedOpenAcyclicSupportedEquivalence j T).isEquivalence_inverse

/-- Flattening is exact for the original inherited fine weak equivalences. -/
theorem perfectSupportedOpenAcyclicToSupported_exact :
    IsExact (acyclicStructure (perfectSupportedOpenNested j T)).cof
      (acyclicStructure (perfectSupportedOpenNested j T)).weq
      (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof (perfectSupportedWaldhausen (T ⊔
        j.opensRange).ι).weq
      (perfectSupportedOpenAcyclicToSupported j T) where
  zero h := IsZero.of_full_of_faithful_of_isZero (perfectSupportedUnionToAcyclic j T) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (perfectSupportedOpenAcyclicToSupported j T)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
theorem perfectSupportedUnionToAcyclic_exact :
    IsExact (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof (perfectSupportedWaldhausen (T ⊔
      j.opensRange).ι).weq
      (acyclicStructure (perfectSupportedOpenNested j T)).cof
      (acyclicStructure (perfectSupportedOpenNested j T)).weq
      (perfectSupportedUnionToAcyclic j T) where
  zero h := IsZero.of_full_of_faithful_of_isZero (perfectSupportedOpenAcyclicToSupported j T) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (perfectSupportedUnionToAcyclic j T)

/-- The actual supported inclusion is preserved at the functor level. -/
def perfectSupportedOpenAcyclicToSupportedInclusionIso :
    perfectSupportedOpenAcyclicToSupported j T ⋙ ObjectProperty.ιOfLE
      (show perfectSupported (T ⊔ j.opensRange).ι ≤ perfectSupported T.ι from fun K h ↦
        ((perfectSupported_sup_opensRange_iff j T K).mp h).1) ≅
      acyclicInclusion (perfectSupportedOpenNested j T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0331",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Support.lean:36-182"
    "adaptation"
    "Native supported relative-open coarse model and actual maps, without fine-open comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenAcyclicSupportedEquivalence
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenAcyclicToSupported_exact
  AlgebraicGeometry.Scheme.Modules.perfectSupportedUnionToAcyclic_exact
