/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedSections
public import Colib.CategoryTheory.Waldhausen.SubcategoryInclusion

/-!
# The original supported global section structure and forgetful map

These are structures on the actual supported subcategory of the existing global sections.
The strict zero-preserving diagram interface does not replace Stacks perfect complexes.
Coefficient restriction from the later part of the source requires its separate joint-index closure.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry.RingedSpace
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The original global chosen zero satisfies actual support on every open. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:41"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalZero_supported :
    boundedAboveFlatGlobalSectionSupported j (boundedAboveFlatGlobalSectionWaldhausen X).zero :=
  HomologicalComplex.acyclic_of_isZero _
    (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
    ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).ι.map_isZero
      ((boundedAboveFlatGlobalSectionEvaluation_exact X).zero
        (boundedAboveFlatGlobalSectionWaldhausen X).isZero)))

/-- The supported zero keeps the original global section literally. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:47"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedZero : (boundedAboveFlatGlobalSectionSupported
  j).FullSubcategory :=
  ⟨(boundedAboveFlatGlobalSectionWaldhausen X).zero, boundedAboveFlatGlobalZero_supported j⟩

/-- Original supported evaluation sends this unchanged chosen zero to zero. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:51"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedZero_evaluation_isZero :
    IsZero ((boundedAboveFlatGlobalSupportedEvaluation j).obj
      (boundedAboveFlatGlobalSupportedZero j)) :=
  IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatPerfectSupported j).ι _
    ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).ι.map_isZero
      ((boundedAboveFlatGlobalSectionEvaluation_exact X).zero
        (boundedAboveFlatGlobalSectionWaldhausen X).isZero))

/-- Original supported classes with the actual restricted global zero. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:58"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedWaldhausen :
    Structure (boundedAboveFlatGlobalSectionSupported j).FullSubcategory :=
  (boundedAboveFlatPerfectSupportedWaldhausen j).ofEquivalence
    (boundedAboveFlatGlobalSupportedEvaluation j).asEquivalence
      (boundedAboveFlatGlobalSupportedZero j)
    (boundedAboveFlatGlobalSupportedZero_evaluation_isZero j)

/-- The same supported sections with their native strict zero-preserving diagram interface. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:64"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedSectionModel : WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := (boundedAboveFlatGlobalSectionSupported j).FullSubcategory,
     waldhausen := boundedAboveFlatGlobalSupportedWaldhausen j }⟩

/-- Supported evaluation is exact for the unchanged geometric classes. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:68"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedEvaluation_exact :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen j).cof
      (boundedAboveFlatGlobalSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
        (boundedAboveFlatGlobalSupportedEvaluation j) :=
  Structure.ofEquivalence_exact _ _ _ _

/-- Supported evaluation commutes with the actual geometric inclusion. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:75"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedEvaluation_forget :
    boundedAboveFlatGlobalSupportedEvaluation j ⋙ ObjectProperty.ιOfLE
      (show boundedAboveFlatPerfectSupported j ≤ boundedAboveFlatPerfectComplex
        X.unop.toRingedSpace from fun _ h => h.1) =
      (boundedAboveFlatGlobalSectionSupported j).ι ⋙ boundedAboveFlatGlobalSectionEvaluation X := by
  unfold boundedAboveFlatGlobalSupportedEvaluation
  rfl

/-- Forgetting support is exact after original evaluation. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:86"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedForget_evaluation_exact :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen j).cof
      (boundedAboveFlatGlobalSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).weq
      ((boundedAboveFlatGlobalSectionSupported j).ι ⋙ boundedAboveFlatGlobalSectionEvaluation
        X) := by
  let := boundedAboveFlatPerfectComplex_containsZero (X := X.unop.toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderIsomorphisms (X := X.unop.toRingedSpace)
  let : (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex X.unop.Modules ℤ)).IsExtensionClosed
        (boundedAboveFlatPerfectComplex X.unop.toRingedSpace) :=
    boundedAboveFlatPerfectComplex_extensionClosed (X := X.unop.toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderFiniteProducts (X := X.unop.toRingedSpace)
  rw [← boundedAboveFlatGlobalSupportedEvaluation_forget j]
  exact (boundedAboveFlatGlobalSupportedEvaluation_exact j).comp
    (subcategoryInclusion_exact (A := X.unop.Modules)
      (boundedAboveFlatPerfectSupported j)
      (boundedAboveFlatPerfectComplex X.unop.toRingedSpace) (fun _ h => h.1))

/-- Forgetting support is exact for the original global structure. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:96"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedForget_exact :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen j).cof
      (boundedAboveFlatGlobalSupportedWaldhausen j).weq
      (boundedAboveFlatGlobalSectionWaldhausen X).cof
        (boundedAboveFlatGlobalSectionWaldhausen X).weq
      (boundedAboveFlatGlobalSectionSupported j).ι where
  zero hz := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatGlobalSectionEvaluation X) _
    ((boundedAboveFlatGlobalSupportedForget_evaluation_exact j).zero hz)
  cofibration f hf := (boundedAboveFlatGlobalSupportedForget_evaluation_exact j).cofibration f hf
  weak f hf := (boundedAboveFlatGlobalSupportedForget_evaluation_exact j).weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful (boundedAboveFlatGlobalSectionEvaluation X)
    ((boundedAboveFlatGlobalSupportedForget_evaluation_exact j).pushout hi hp)

/-- Forgetting support preserves the actual global zero literally. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedModels.lean:108"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedForget : boundedAboveFlatGlobalSupportedSectionModel j ⟶
    boundedAboveFlatGlobalSectionModel X :=
  ⟨⟨(boundedAboveFlatGlobalSectionSupported j).ι,
    boundedAboveFlatGlobalSupportedForget_exact j⟩, rfl⟩


end AlgebraicGeometry.Scheme.Modules
