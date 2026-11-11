/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitAction
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport

/-!
# The actual tensor-unit action with original acyclic support

The original support property is acyclicity after restriction to the specified open. The actual
tensor left unitor preserves that property and restricts the tensor/scalar square to the full
supported category, without changing any underlying complex or chain map.

The native supported full subcategory keeps the original open-restriction acyclicity.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open MonoidalCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Native sheaf tensor on the unchanged scheme module category. -/
local instance supportedTensorUnitMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
/-- Native additive tensor structure used for degreewise complexes. -/
local instance supportedTensorUnitPreadditive (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual acyclicity after the original open restriction is preserved by unit tensor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:34"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
theorem boundedAboveFlatPerfectTensorUnit_supported {K : CochainComplex X.Modules ℤ}
    (hK : boundedAboveFlatPerfectSupported j K) :
    boundedAboveFlatPerfectSupported j
      (((MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ)).obj K) :=
  (boundedAboveFlatPerfectSupported j).prop_of_iso ((complexTensorUnitIso X).app K).symm hK

/-- Genuine structure-module tensor on the original supported full subcategory. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:41"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnit :
    (boundedAboveFlatPerfectSupported j).FullSubcategory ⥤
      (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  (boundedAboveFlatPerfectSupported j).lift
    ((boundedAboveFlatPerfectSupported j).ι ⋙
      (MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ))
    (fun K ↦ boundedAboveFlatPerfectTensorUnit_supported j K.property)

/-- The original tensor unitor restricted to the acyclic-support category. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:49"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnitIso :
    boundedAboveFlatPerfectSupportedTensorUnit j ≅
      𝟭 (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported j).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported j).ι (complexTensorUnitIso X))

/-- The unchanged structure-module coefficient action on supported complexes. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:55"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnitAutomorphism (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectSupportedTensorUnit j ≅ boundedAboveFlatPerfectSupportedTensorUnit j :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported j).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported j).ι
      (complexTensorUnitAutomorphism X r))

/-- Restrict the existing forward scalar automorphism to actual supported complexes. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:61"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedGlobalUnitIso (r : (Γ(X, ⊤))ˣ) :
    𝟭 (boundedAboveFlatPerfectSupported j).FullSubcategory ≅
      𝟭 (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported j).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported j).ι (complexGlobalUnitIso X r))

/-- Forgetting support retains the original coefficient tensor map on the underlying complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:68"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
theorem boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_hom_original
    (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectSupported j).FullSubcategory) :
    (boundedAboveFlatPerfectSupported j).ι.map
        ((boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app K) =
      (complexTensorUnitAutomorphism X r).hom.app K.obj := by
  simp only [boundedAboveFlatPerfectSupportedTensorUnitAutomorphism,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]

/-- The whole actual tensor/scalar square restricts to original supported complexes. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitSupport.lean:78"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
theorem boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_unitor (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom ≫
        (boundedAboveFlatPerfectSupportedTensorUnitIso j).hom =
      (boundedAboveFlatPerfectSupportedTensorUnitIso j).hom ≫
        (boundedAboveFlatPerfectSupportedGlobalUnitIso j r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedAboveFlatPerfectSupported j).ι.map_injective
  simp only [NatTrans.comp_app, Functor.map_comp,
    boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_hom_original,
    boundedAboveFlatPerfectSupportedTensorUnitIso, boundedAboveFlatPerfectSupportedGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
  exact NatTrans.congr_app (complexTensorUnitAutomorphism_unitor X r) K.obj

end AlgebraicGeometry.Scheme.Modules
