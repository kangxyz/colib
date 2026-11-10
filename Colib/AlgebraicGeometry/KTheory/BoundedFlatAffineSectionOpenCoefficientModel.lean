/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenReindexExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenModel

/-!
# Actual relative-open coefficient Model arrows

The unchanged section reindexing and original chosen section zeros give genuine Model maps
for each specified commuting open-pair square. Identity and composition use the same original
strict section functors. The original fine-to-coarse maps commute literally with reindexing;
no geometric evaluation equality or independently chosen zero identification is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.StrictSections CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}

/-- The original coefficient reindexing with its actual coarse exactness and section zero. -/
def boundedAboveFlatAffineSectionOpenReindexModelMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedAboveFlatAffineSectionOpenModel j ⟶ boundedAboveFlatAffineSectionOpenModel j' :=
  ⟨⟨boundedAboveFlatAffineSectionsMap f, boundedAboveFlatAffineSectionsMap_open_exact j j' f l h⟩,
    (boundedAboveFlatAffineSectionModelMap f).property⟩

/-- The identity coefficient map retains the unchanged relative-open section Model. -/
theorem boundedAboveFlatAffineSectionOpenReindexModelMap_id
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (h : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedAboveFlatAffineSectionOpenReindexModelMap j j (𝟙 R) (𝟙 U) h =
      𝟙 (boundedAboveFlatAffineSectionOpenModel j) := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  exact boundedAboveFlatAffineSectionsMap_id R

/-- Composition keeps the specified original coefficient and open maps. -/
theorem boundedAboveFlatAffineSectionOpenReindexModelMap_comp
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) (j'' : W ⟶ Spec T)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : R ⟶ S) (g : S ⟶ T) (l : V ⟶ U) (m : W ⟶ V)
    (hf : l ≫ j = j' ≫ Spec.map f) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedAboveFlatAffineSectionOpenReindexModelMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedAboveFlatAffineSectionOpenReindexModelMap j j' f l hf ≫
        boundedAboveFlatAffineSectionOpenReindexModelMap j' j'' g m hg := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  exact boundedAboveFlatAffineSectionsMap_comp f g

/-- The original fine-to-coarse Model maps commute with the unchanged coefficient reindexing. -/
theorem boundedAboveFlatAffineSectionOpenModelMap_naturality
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedAboveFlatAffineSectionModelMap f ≫ boundedAboveFlatAffineSectionOpenModelMap j' =
      boundedAboveFlatAffineSectionOpenModelMap j ≫
        boundedAboveFlatAffineSectionOpenReindexModelMap j j' f l h := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  exact (Functor.comp_id _).trans (Functor.id_comp _).symm

/-- The actual relative-open coefficient prespectrum map retains the original Model arrow. -/
def boundedAboveFlatAffineSectionOpenReindexPrespectrumMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    prespectrum (boundedAboveFlatAffineSectionOpenModel j) ⟶
      prespectrum (boundedAboveFlatAffineSectionOpenModel j') :=
  prespectrumMap (boundedAboveFlatAffineSectionOpenReindexModelMap j j' f l h)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenCoefficientModel.lean:28-74"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenReindexModelMap
  boundedAboveFlatAffineSectionOpenReindexModelMap_id
  boundedAboveFlatAffineSectionOpenReindexModelMap_comp
  boundedAboveFlatAffineSectionOpenModelMap_naturality
  boundedAboveFlatAffineSectionOpenReindexPrespectrumMap

end AlgebraicGeometry.Scheme.Modules
