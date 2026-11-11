/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.TensorUnitScalar
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit

/-! # Degreewise tensor-unit automorphisms on native bounded-above flat perfect complexes

Migrated from Quillen's `BoundedFlat/TensorUnitAction.lean`, pinned at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Tensor products and unitors are the native
Stacks sheaf tensor; the existing full subcategory is unchanged.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open Stacks.RegularSequence (globalSmulCenter)
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The native sheaf-of-modules monoidal structure on the scheme. -/
local instance boundedFlatPerfectTensorUnitActionMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance boundedFlatPerfectTensorUnitActionPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

/-- The actual sheaf global unit, before applying the coefficient tensor functor. -/
def tensorCoefficientUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟙_ X.Modules ≅ 𝟙_ X.Modules where
  hom := (globalSmulCenter X (r : Γ(X, ⊤))).app _
  inv := (globalSmulCenter X (↑(r⁻¹) : Γ(X, ⊤))).app _
  hom_inv_id := by
    ext U m
    simp [Stacks.RegularSequence.globalSmulCenter_app_app, ← mul_assoc, ← map_mul]
  inv_hom_id := by
    ext U m
    simp [Stacks.RegularSequence.globalSmulCenter_app_app, ← mul_assoc, ← map_mul]

/-- The original sheaf tensor left unitor, applied in every complex degree. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:35"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def complexTensorUnitIso (X : Scheme.{u}) :
    (MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex X.Modules ℤ) :=
  NatIso.mapHomologicalComplex (MonoidalCategory.leftUnitorNatIso X.Modules) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)

/-- The actual coefficient tensor of the original structure-module automorphism. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:42"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def complexTensorUnitAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ) ≅
      (MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ) :=
  let e : MonoidalCategory.tensorLeft (𝟙_ X.Modules) ≅
      MonoidalCategory.tensorLeft (𝟙_ X.Modules) :=
    (MonoidalCategory.curriedTensor X.Modules).mapIso (tensorCoefficientUnitIso X r)
  NatIso.mapHomologicalComplex e (.up ℤ)

/-- The complex unitor retains the genuine sheaf unitor in each degree. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:51"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem complexTensorUnitIso_hom_f (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((complexTensorUnitIso X).hom.app K).f n =
      (MonoidalCategory.leftUnitorNatIso X.Modules).hom.app (K.X n) := by
  change (MonoidalCategory.leftUnitorNatIso X.Modules).hom.app (K.X n) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The automorphism retains the original coefficient tensor map in each degree. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:59"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem complexTensorUnitAutomorphism_hom_f (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((complexTensorUnitAutomorphism X r).hom.app K).f n =
      ((globalSmulCenter X (r : Γ(X, ⊤))).app (𝟙_ X.Modules) ▷ K.X n) := rfl

/-- The original tensor-unit automorphism is the forward scalar under the actual unitor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:65"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem complexTensorUnitAutomorphism_unitor (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (complexTensorUnitAutomorphism X r).hom ≫ (complexTensorUnitIso X).hom =
      (complexTensorUnitIso X).hom ≫ (complexGlobalUnitIso X r).hom := by
  apply NatTrans.ext
  funext K
  ext n : 1
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    complexTensorUnitAutomorphism_hom_f, complexTensorUnitIso_hom_f,
    complexGlobalUnitIso, complexGlobalScalar_app_f]
  exact tensorUnit_globalScalar_unitor X (r : Γ(X, ⊤)) (K.X n)

/-- Genuine degreewise tensor by the structure module on the bounded-flat perfect subcategory. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:77"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def boundedAboveFlatPerfectTensorUnit (X : Scheme.{u}) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  (boundedAboveFlatPerfectComplex X.toRingedSpace).lift
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι ⋙ (MonoidalCategory.tensorLeft (𝟙_
      X.Modules)).mapHomologicalComplex (.up ℤ))
    (fun K => boundedAboveFlatPerfectComplex_of_iso ((complexTensorUnitIso X).app K.obj).symm
      K.property)

/-- The same left unitor in the original bounded-flat full subcategory. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:84"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def boundedAboveFlatPerfectTensorUnitIso (X : Scheme.{u}) :
    boundedAboveFlatPerfectTensorUnit X ≅ 𝟭 ((boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
      (complexTensorUnitIso X))

/-- Tensor the original structure-module unit automorphism on every bounded-flat input. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:90"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def boundedAboveFlatPerfectTensorUnitAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectTensorUnit X ≅ boundedAboveFlatPerfectTensorUnit X :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
      (complexTensorUnitAutomorphism X r))

/-- Inclusion retains the original complex tensor map, without a replacement identity functor. -/
theorem boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original
    (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
        ((boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom.app K) =
      (complexTensorUnitAutomorphism X r).hom.app K.obj := by
  simp only [boundedAboveFlatPerfectTensorUnitAutomorphism,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]

/-- The actual full-subcategory unitor keeps its original ambient component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitAction.lean:106"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem boundedAboveFlatPerfectTensorUnitIso_hom_original (X : Scheme.{u})
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map ((boundedAboveFlatPerfectTensorUnitIso
      X).hom.app K) =
      (complexTensorUnitIso X).hom.app K.obj := by
  simp only [boundedAboveFlatPerfectTensorUnitIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj]

/-- The entire natural transformation, hence every morphism, keeps the original forward scalar. -/
theorem boundedAboveFlatPerfectTensorUnitAutomorphism_unitor
    (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom ≫
        (boundedAboveFlatPerfectTensorUnitIso X).hom =
      (boundedAboveFlatPerfectTensorUnitIso X).hom ≫ (boundedAboveFlatPerfectGlobalUnitIso X
      r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  simp only [NatTrans.comp_app, Functor.map_comp,
    boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original,
    boundedAboveFlatPerfectTensorUnitIso_hom_original,
      boundedAboveFlatPerfectGlobalUnitIso_hom_original]
  exact NatTrans.congr_app (complexTensorUnitAutomorphism_unitor X r) K.obj

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0542"] boundedAboveFlatPerfectTensorUnitAutomorphism_unitor

end AlgebraicGeometry.Scheme.Modules
