/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpen
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedApproximation
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedClosure

/-!
# Supported bounded-flat complexes as actual relative acyclics

The original relative-acyclic category is exactly equivalent to the supported
bounded-flat full subcategory. Cofibrations retain their genuine supported
quotients, as proved by exact restriction and its homology sequence.
-/
@[expose] public section

open CategoryTheory.Waldhausen

open AlgebraicGeometry.RingedSpace

open CategoryTheory.ExactCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Relative coarse acyclicity is the actual support predicate, in every degree. -/
theorem boundedAboveFlatPerfectOpenAcyclic_iff (K : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory) :
    Acyclic (boundedAboveFlatPerfectOpenWaldhausen j) K ↔ (((restrictFunctor
      j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).Acyclic := by
  have hZ : IsZero (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero.obj) :=
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_isZero
      (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace).isZero)
  change QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero.to_ K).hom) ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Forget the redundant nested full-subcategory wrapper. -/
def boundedAboveFlatPerfectAcyclicToSupported :
    AcyclicCategory (boundedAboveFlatPerfectOpenNested j) ⥤ (boundedAboveFlatPerfectSupported
      j).FullSubcategory where
  obj K := ⟨K.obj.obj, K.obj.property, (boundedAboveFlatPerfectOpenAcyclic_iff j K.obj).1
    K.property⟩
  map f := (boundedAboveFlatPerfectSupported j).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def boundedAboveFlatPerfectSupportedToAcyclic :
    (boundedAboveFlatPerfectSupported j).FullSubcategory ⥤ AcyclicCategory
      (boundedAboveFlatPerfectOpenNested
      j) where
  obj K := ⟨⟨K.obj, K.property.1⟩,
    (boundedAboveFlatPerfectOpenAcyclic_iff j ⟨K.obj, K.property.1⟩).2 K.property.2⟩
  map f := (acyclicObjects (boundedAboveFlatPerfectOpenNested j)).homMk
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).homMk
    f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem boundedAboveFlatPerfectAcyclicToSupported_obj
    (K : AcyclicCategory (boundedAboveFlatPerfectOpenNested j)) :
    ((boundedAboveFlatPerfectAcyclicToSupported j).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem boundedAboveFlatPerfectAcyclicToSupported_map
    {K L : AcyclicCategory (boundedAboveFlatPerfectOpenNested j)} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectAcyclicToSupported j).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem boundedAboveFlatPerfectSupportedToAcyclic_obj
    (K : (boundedAboveFlatPerfectSupported j).FullSubcategory) :
    ((boundedAboveFlatPerfectSupportedToAcyclic j).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem boundedAboveFlatPerfectSupportedToAcyclic_map
    {K L : (boundedAboveFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectSupportedToAcyclic j).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem boundedAboveFlatPerfectAcyclicToSupported_comp_inverse :
    boundedAboveFlatPerfectAcyclicToSupported j ⋙ boundedAboveFlatPerfectSupportedToAcyclic j =
      𝟭 (AcyclicCategory (boundedAboveFlatPerfectOpenNested j)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem boundedAboveFlatPerfectSupportedToAcyclic_comp_inverse :
    boundedAboveFlatPerfectSupportedToAcyclic j ⋙ boundedAboveFlatPerfectAcyclicToSupported j =
      𝟭 ((boundedAboveFlatPerfectSupported j).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem boundedAboveFlatPerfectAcyclicToSupported_comp_inclusion :
    boundedAboveFlatPerfectAcyclicToSupported j ⋙ boundedAboveFlatPerfectSupportedForget j =
      acyclicInclusion (boundedAboveFlatPerfectOpenNested j) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem boundedAboveFlatPerfectSupportedToAcyclic_comp_inclusion :
    boundedAboveFlatPerfectSupportedToAcyclic j ⋙ acyclicInclusion
      (boundedAboveFlatPerfectOpenNested j) =
      boundedAboveFlatPerfectSupportedForget j := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
def boundedAboveFlatPerfectAcyclicSupportedEquivalence :
    AcyclicCategory (boundedAboveFlatPerfectOpenNested j) ≌ (boundedAboveFlatPerfectSupported
      j).FullSubcategory where
  functor := boundedAboveFlatPerfectAcyclicToSupported j
  inverse := boundedAboveFlatPerfectSupportedToAcyclic j
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)

local instance : (boundedAboveFlatPerfectAcyclicToSupported j).IsEquivalence :=
  (boundedAboveFlatPerfectAcyclicSupportedEquivalence j).isEquivalence_functor
local instance : (boundedAboveFlatPerfectSupportedToAcyclic j).IsEquivalence :=
  (boundedAboveFlatPerfectAcyclicSupportedEquivalence j).isEquivalence_inverse

/-- A fine cofibration between supported objects has a supported quotient. -/
theorem boundedAboveFlatPerfectAcyclicToSupported_cofibration
    {A B : AcyclicCategory (boundedAboveFlatPerfectOpenNested j)} (f : A ⟶ B)
    (hf : (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).cof f) :
    (boundedAboveFlatPerfectSupportedWaldhausen j).cof ((boundedAboveFlatPerfectAcyclicToSupported
      j).map f)
      := by
  obtain ⟨Q, hQ, q, w, hS⟩ :=
    (boundedAboveFlatPerfectWaldhausen_cof_iff X.toRingedSpace f.hom).1 hf
  have hQu : perfectSupported j Q :=
    perfectSupported_X₃_of_shortExact j hS
      ⟨A.obj.property.1, (boundedAboveFlatPerfectOpenAcyclic_iff j A.obj).1 A.property⟩
      ⟨B.obj.property.1, (boundedAboveFlatPerfectOpenAcyclic_iff j B.obj).1 B.property⟩
  exact (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff j _).2
    ⟨Q, ⟨hQ, hQu.2⟩, q, w, hS⟩

/-- Flattening is exact for the original inherited fine weak equivalences. -/
theorem boundedAboveFlatPerfectAcyclicToSupported_exact :
    IsExact (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
        (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectAcyclicToSupported j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatPerfectSupportedToAcyclic j) _ h
  cofibration f h := boundedAboveFlatPerfectAcyclicToSupported_cofibration j f h
  weak _ h := h
  pushout _ h := h.map (boundedAboveFlatPerfectAcyclicToSupported j)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
theorem boundedAboveFlatPerfectSupportedToAcyclic_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen
      j).weq
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).weq
      (boundedAboveFlatPerfectSupportedToAcyclic j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatPerfectAcyclicToSupported j) _ h
  cofibration f h := by
    obtain ⟨Q, hQ, q, w, hS⟩ :=
      (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff j f).1 h
    exact (boundedAboveFlatPerfectWaldhausen_cof_iff X.toRingedSpace _).2
      ⟨Q, hQ.1, q, w, hS⟩
  weak _ h := h
  pushout _ h := h.map (boundedAboveFlatPerfectSupportedToAcyclic j)

/-- The actual supported inclusion is preserved at the functor level. -/
def boundedAboveFlatPerfectAcyclicToSupportedInclusionIso :
    boundedAboveFlatPerfectAcyclicToSupported j ⋙ boundedAboveFlatPerfectSupportedForget j ≅
      acyclicInclusion (boundedAboveFlatPerfectOpenNested j) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenSupport.lean:42-180"
  "adaptation" "The actual relative-acyclic and supported equivalence with exact quotient classes"]
  boundedAboveFlatPerfectOpenAcyclic_iff
  boundedAboveFlatPerfectAcyclicToSupported
  boundedAboveFlatPerfectSupportedToAcyclic
  boundedAboveFlatPerfectAcyclicToSupported_obj
  boundedAboveFlatPerfectAcyclicToSupported_map
  boundedAboveFlatPerfectSupportedToAcyclic_obj
  boundedAboveFlatPerfectSupportedToAcyclic_map
  boundedAboveFlatPerfectAcyclicToSupported_comp_inverse
  boundedAboveFlatPerfectSupportedToAcyclic_comp_inverse
  boundedAboveFlatPerfectAcyclicToSupported_comp_inclusion
  boundedAboveFlatPerfectSupportedToAcyclic_comp_inclusion
  boundedAboveFlatPerfectAcyclicSupportedEquivalence
  boundedAboveFlatPerfectAcyclicToSupported_cofibration
  boundedAboveFlatPerfectAcyclicToSupported_exact
  boundedAboveFlatPerfectSupportedToAcyclic_exact
  boundedAboveFlatPerfectAcyclicToSupportedInclusionIso

end AlgebraicGeometry.Scheme.Modules
