/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpen
public import Colib.AlgebraicGeometry.Modules.PerfectSupportUnion

/-!
# Actual union support for bounded-flat relative acyclics

The actual relative-acyclic category is exactly equivalent to bounded-flat perfect complexes
acyclic on the union of the two opens. The quotient of every inherited cofibration retains
bounded flatness and both acyclicity conditions. No compactness hypothesis is used.

Adapted from Quillen `BoundedFlat/SupportedOpenFibration.lean:50-200` and
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/SupportUnion.lean:36-42`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native sheaf restriction and homology.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Actual vanishing on the union preserves the same bounded-flat perfect complex. -/
theorem boundedAboveFlatPerfectSupported_sup_opensRange_iff (K : CochainComplex X.Modules ℤ) :
    boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι K ↔
      boundedAboveFlatPerfectSupported T.ι K ∧
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  simp only [boundedAboveFlatPerfectSupported, restrictAcyclic_sup_iff,
    restrictAcyclic_opensRange_iff]
  exact and_assoc.symm

/-- Relative coarse acyclicity is the actual support predicate, in every degree. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclic_iff
    (K : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory) :
    Acyclic (boundedAboveFlatPerfectSupportedOpenWaldhausen j T) K ↔
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).Acyclic := by
  have hZ : IsZero (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι).zero.obj) :=
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      ((boundedAboveFlatPerfectSupported T.ι).ι.map_isZero
        (boundedAboveFlatPerfectSupportedWaldhausen T.ι).isZero)
  change QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((boundedAboveFlatPerfectSupportedWaldhausen T.ι).isZero.to_ K).hom) ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Forget the redundant nested full-subcategory wrapper. -/
def boundedAboveFlatPerfectSupportedOpenAcyclicToSupported :
    AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T) ⥤
      (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory where
  obj K := ⟨K.obj.obj, (boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K.obj.obj).mpr
    ⟨K.obj.property, (boundedAboveFlatPerfectSupportedOpenAcyclic_iff j T K.obj).1 K.property⟩⟩
  map f := (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def boundedAboveFlatPerfectSupportedUnionToAcyclic :
    (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory ⥤ AcyclicCategory
      (boundedAboveFlatPerfectSupportedOpenNested j T) where
  obj K := ⟨⟨K.obj,
    ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K.obj).mp K.property).1⟩,
    (boundedAboveFlatPerfectSupportedOpenAcyclic_iff j T _).2
      ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K.obj).mp K.property).2⟩
  map f := (acyclicObjects (boundedAboveFlatPerfectSupportedOpenNested j T)).homMk
    ((boundedAboveFlatPerfectSupported T.ι).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_obj
    (K : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)) :
    ((boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_map
    {K L : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem boundedAboveFlatPerfectSupportedUnionToAcyclic_obj
    (K : (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) :
    ((boundedAboveFlatPerfectSupportedUnionToAcyclic j T).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem boundedAboveFlatPerfectSupportedUnionToAcyclic_map
    {K L : (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectSupportedUnionToAcyclic j T).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_comp_inverse :
    boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T ⋙
      boundedAboveFlatPerfectSupportedUnionToAcyclic j T =
      𝟭 (AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem boundedAboveFlatPerfectSupportedUnionToAcyclic_comp_inverse :
    boundedAboveFlatPerfectSupportedUnionToAcyclic j T ⋙
      boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T =
      𝟭 ((boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_comp_inclusion :
    boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T ⋙ ObjectProperty.ιOfLE
      (show boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι ≤
        boundedAboveFlatPerfectSupported T.ι from fun K h ↦
        ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) =
      acyclicInclusion (boundedAboveFlatPerfectSupportedOpenNested j T) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem boundedAboveFlatPerfectSupportedUnionToAcyclic_comp_inclusion :
    boundedAboveFlatPerfectSupportedUnionToAcyclic j T ⋙
      acyclicInclusion (boundedAboveFlatPerfectSupportedOpenNested j T) =
      ObjectProperty.ιOfLE
        (show boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι ≤
        boundedAboveFlatPerfectSupported T.ι from fun K h ↦
          ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
@[colib_tag "COL-0506",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:64-141"
    "adaptation"
    "Actual relative-acyclic and union-supported bounded-flat categories with original maps"]
def boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence :
    AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T) ≌
      (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory where
  functor := boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T
  inverse := boundedAboveFlatPerfectSupportedUnionToAcyclic j T
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)

local instance : (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T).IsEquivalence :=
  (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).isEquivalence_functor
local instance : (boundedAboveFlatPerfectSupportedUnionToAcyclic j T).IsEquivalence :=
  (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).isEquivalence_inverse

/-- The original admissible quotient retains both actual acyclicity conditions. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_cofibration
    {A B : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)} (f : A ⟶ B)
    (hf : (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).cof f) :
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      ((boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T).map f) := by
  obtain ⟨Q, hQ, q, w, hS⟩ :=
    (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff T.ι f.hom).1 hf
  have hQu : perfectSupported j Q :=
    perfectSupported_X₃_of_shortExact j hS
      ⟨A.obj.property.1.1,
        (boundedAboveFlatPerfectSupportedOpenAcyclic_iff j T A.obj).1 A.property⟩
      ⟨B.obj.property.1.1,
        (boundedAboveFlatPerfectSupportedOpenAcyclic_iff j T B.obj).1 B.property⟩
  exact (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff (T ⊔ j.opensRange).ι _).2
    ⟨Q, (boundedAboveFlatPerfectSupported_sup_opensRange_iff j T Q).2 ⟨hQ, hQu.2⟩,
      q, w, hS⟩

/-- Flattening is exact for the original inherited fine weak equivalences. -/
@[colib_tag "COL-0506",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:149-179"
    "adaptation"
    "Exact flattening preserves the actual bounded-flat quotient and both support conditions"]
theorem boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact :
    IsExact (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).cof
      (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).weq
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
      (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T) where
  zero h := IsZero.of_full_of_faithful_of_isZero
    (boundedAboveFlatPerfectSupportedUnionToAcyclic j T) _ h
  cofibration f h := boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_cofibration j T f h
  weak _ h := h
  pushout _ h := h.map (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
@[colib_tag "COL-0506",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:182-194"
    "adaptation"
    "Exact inverse retains the same quotient, fine weak class and original underlying maps"]
theorem boundedAboveFlatPerfectSupportedUnionToAcyclic_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
      (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).cof
      (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).weq
      (boundedAboveFlatPerfectSupportedUnionToAcyclic j T) where
  zero h := IsZero.of_full_of_faithful_of_isZero
    (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T) _ h
  cofibration f h := by
    obtain ⟨Q, hQ, q, w, hS⟩ :=
      (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff (T ⊔ j.opensRange).ι f).1 h
    exact (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff T.ι _).2
      ⟨Q, ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T Q).1 hQ).1, q, w, hS⟩
  weak _ h := h
  pushout _ h := h.map (boundedAboveFlatPerfectSupportedUnionToAcyclic j T)

/-- The actual supported inclusion is preserved at the functor level. -/
def boundedAboveFlatPerfectSupportedOpenAcyclicToSupportedInclusionIso :
    boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T ⋙ ObjectProperty.ιOfLE
      (show boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι ≤
        boundedAboveFlatPerfectSupported T.ι from fun K h ↦
        ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) ≅
      acyclicInclusion (boundedAboveFlatPerfectSupportedOpenNested j T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)

end AlgebraicGeometry.Scheme.Modules
