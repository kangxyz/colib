/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionReindexExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedEvaluationComparison

/-!
# Original supported section models and coefficient maps

The actual supported section category, its proved Waldhausen structure and original chosen
zero give an iterated-S model. Exact original coefficient reindexing gives literal model maps
for every specified affine open-pair square. Their identity and composition laws retain the
actual coefficient and open-side maps. This construction does not strictify geometric evaluation.
Adapted from Quillen `BoundedFlat/SupportedSectionModel.lean:37-73` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}

/-- Original supported coefficient reindexing gives an exact, literally zero-preserving model map.
-/
def boundedAboveFlatAffineSupportedSectionModelMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedAboveFlatAffineSupportedSectionModel j ⟶
      boundedAboveFlatAffineSupportedSectionModel j' :=
  ⟨⟨boundedAboveFlatAffineSupportedSectionsMap j j' f l h,
    boundedAboveFlatAffineSupportedSectionsMap_exact j j' f l h⟩,
    boundedAboveFlatAffineSupportedSectionsMap_sectionZero j j' f l h⟩

/-- The native model map retains the actual supported restriction functor. -/
theorem boundedAboveFlatAffineSupportedSectionModelMap_toFunctor
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    (boundedAboveFlatAffineSupportedSectionModelMap j j' f l h).hom.toFunctor =
      boundedAboveFlatAffineSupportedSectionsMap j j' f l h := rfl

/-- Identity uses the same supported section model and original coefficient functor. -/
theorem boundedAboveFlatAffineSupportedSectionModelMap_id
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (h : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedAboveFlatAffineSupportedSectionModelMap j j (𝟙 R) (𝟙 U) h =
      𝟙 (boundedAboveFlatAffineSupportedSectionModel j) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact boundedAboveFlatAffineSupportedSectionsMap_id j h

/-- Composition preserves the entire original specified affine open-pair square. -/
theorem boundedAboveFlatAffineSupportedSectionModelMap_comp
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) (j'' : W ⟶ Spec T)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : R ⟶ S) (g : S ⟶ T) (l : V ⟶ U) (m : W ⟶ V)
    (hf : l ≫ j = j' ≫ Spec.map f) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedAboveFlatAffineSupportedSectionModelMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedAboveFlatAffineSupportedSectionModelMap j j' f l hf ≫
        boundedAboveFlatAffineSupportedSectionModelMap j' j'' g m hg := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact boundedAboveFlatAffineSupportedSectionsMap_comp j j' j'' f g l m hf hg hfg

/-- The original iterated-S map on actual supported sections. -/
def boundedAboveFlatAffineSupportedSectionPrespectrumMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    prespectrum (boundedAboveFlatAffineSupportedSectionModel j) ⟶
      prespectrum (boundedAboveFlatAffineSupportedSectionModel j') :=
  prespectrumMap (boundedAboveFlatAffineSupportedSectionModelMap j j' f l h)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionModel.lean:37-73"
  "adaptation"
  "Native chosen-zero `Model` maps of actual reindexing with strict identity and composition"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionModelMap
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionModelMap_toFunctor
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionModelMap_id
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionModelMap_comp
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionPrespectrumMap
