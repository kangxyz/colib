/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedSections
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionPrespectrum
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback

/-!
# Actual supported sections on the joint native coefficient family

A support condition is actual acyclicity of the original evaluated complex on
its specified open. The original identity evaluation restricts to a genuine
equivalence with supported bounded-flat complexes. Its Waldhausen structure
uses the restriction of the same joint global zero section.

Every commuting support square over an original joint index arrow restricts
the original section reindexing to an exact, literally zero-preserving functor.
The constructions impose no compactness or flatness condition on the schemes
or coefficient maps. They supply no supported density or quotient theorem.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace HomologicalComplex
variable {R : CommRingCat.{u}} {i k t : Index R} {U V W : Scheme.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- The one joint global zero section is supported on every specified open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:49"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSectionZero_supported
    (j : U ⟶ space i) [IsOpenImmersion j] :
    boundedAboveFlatCoefficientSectionSupported j (boundedAboveFlatCoefficientSectionZero i) := by
  change (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((boundedAboveFlatCoefficientOriginalEvaluation i).obj
    (boundedAboveFlatCoefficientSectionZero i)).obj).Acyclic
  rw [boundedAboveFlatCoefficientOriginalEvaluation_sectionZero]
  exact HomologicalComplex.acyclic_of_isZero _ (((restrictFunctor j).mapHomologicalComplex
    (ComplexShape.up ℤ)).map_isZero
    ((boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι.map_isZero
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).isZero))

/-- The supported chosen zero is precisely the existing restricted joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:59"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionZero
    (j : U ⟶ space i) [IsOpenImmersion j] : BoundedAboveFlatCoefficientSupportedSections j :=
  ⟨boundedAboveFlatCoefficientSectionZero i, boundedAboveFlatCoefficientSectionZero_supported j⟩

/-- The same joint zero has its actual universal property in the supported category. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:64"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem isZero_boundedAboveFlatCoefficientSupportedSectionZero
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsZero (boundedAboveFlatCoefficientSupportedSectionZero j) :=
  IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatCoefficientSectionSupported j).ι _
    (boundedAboveFlatCoefficientSectionZero_isZero i)

/-- Original supported evaluation carries the same joint zero to a genuine zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:71"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedEvaluation_sectionZero_isZero
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsZero ((boundedAboveFlatCoefficientSupportedEvaluation j).obj
      (boundedAboveFlatCoefficientSupportedSectionZero j)) := by
  apply IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatPerfectSupported j).ι
  change IsZero (((boundedAboveFlatCoefficientOriginalEvaluation i).obj
    (boundedAboveFlatCoefficientSectionZero i)).obj)
  rw [boundedAboveFlatCoefficientOriginalEvaluation_sectionZero]
  exact (boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι.map_isZero
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).isZero

/-- Original supported morphism classes and pushouts retain the one joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:82"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionWaldhausen
    (j : U ⟶ space i) [IsOpenImmersion j] :
    Structure (BoundedAboveFlatCoefficientSupportedSections j) :=
  (boundedAboveFlatPerfectSupportedWaldhausen j).ofEquivalence
    (boundedAboveFlatCoefficientSupportedSectionEquivalence j)
    (boundedAboveFlatCoefficientSupportedSectionZero j) (by
      rw [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedAboveFlatCoefficientSupportedEvaluation_sectionZero_isZero j)

/-- The chosen supported Waldhausen zero retains the original global section. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:92"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionWaldhausen_zero
    (j : U ⟶ space i) [IsOpenImmersion j] :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).zero =
      boundedAboveFlatCoefficientSupportedSectionZero j := rfl

/-- Supported section cofibrations are exactly those of their original evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:98"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionWaldhausen_cof_iff
    (j : U ⟶ space i) [IsOpenImmersion j]
    {S T : BoundedAboveFlatCoefficientSupportedSections j} (f : S ⟶ T) :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof f ↔
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
        ((boundedAboveFlatCoefficientSupportedEvaluation j).map f) := by
  change (boundedAboveFlatPerfectSupportedWaldhausen j).cof
    ((boundedAboveFlatCoefficientSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]

/-- Supported section weak maps are exactly those of their original evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:109"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionWaldhausen_weq_iff
    (j : U ⟶ space i) [IsOpenImmersion j]
    {S T : BoundedAboveFlatCoefficientSupportedSections j} (f : S ⟶ T) :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq f ↔
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
        ((boundedAboveFlatCoefficientSupportedEvaluation j).map f) := by
  change (boundedAboveFlatPerfectSupportedWaldhausen j).weq
    ((boundedAboveFlatCoefficientSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]

/-- The actual forward supported evaluation is Waldhausen-exact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:120"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedEvaluation_exact
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
        (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatCoefficientSupportedEvaluation j) := by
  rw [← boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
  exact Structure.ofEquivalence_exact _ _ _ _

/-- The inverse of the same supported equivalence is Waldhausen-exact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:130"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedAboveFlatCoefficientSupportedSectionEquivalence j).inverse :=
  Structure.ofEquivalence_inverse_exact _ _ _ _

section Reindex
variable (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
  (f : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
include l h

/-- The original joint zero is preserved literally by every supported reindexing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:145"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_sectionZero :
    (boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h).obj
        (boundedAboveFlatCoefficientSupportedSectionZero j) =
      boundedAboveFlatCoefficientSupportedSectionZero j' := by
  apply ObjectProperty.FullSubcategory.ext
  exact boundedAboveFlatCoefficientSectionsMap_sectionZero f

section
attribute [local irreducible] boundedAboveFlatCoefficientSupportedSectionsMap
  boundedAboveFlatCoefficientSupportedEvaluation

end

section
attribute [local irreducible] boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatPerfectSupportedPullback boundedAboveFlatPerfectPullback

end

/-- Supported reindexing detects precisely the weak class of its original geometric pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:165"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_weq_iff
    {S T : BoundedAboveFlatCoefficientSupportedSections j} (p : S ⟶ T) :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j').weq
        ((boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h).map p) ↔
      (boundedAboveFlatPerfectSupportedWaldhausen j').weq
        ((boundedAboveFlatPerfectSupportedPullback
          (boundedAboveFlatCoefficientSupportSquare j j' f l h)).map
            ((boundedAboveFlatCoefficientSupportedEvaluation j).map p)) := by
  rw [boundedAboveFlatCoefficientSupportedSectionWaldhausen_weq_iff]
  let e := Functor.isoWhiskerRight
    (boundedAboveFlatCoefficientSupportedSectionReindexIso j j' f l h)
    (boundedAboveFlatPerfectSupported j').ι
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app S) (e.app T) (e.hom.naturality p).symm)

/-- Supported reindexing followed by the original geometric evaluation is exact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:181"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_evaluation_exact :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j').cof
        (boundedAboveFlatPerfectSupportedWaldhausen j').weq
      (boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        boundedAboveFlatCoefficientSupportedEvaluation j') :=
  ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j)
      (boundedAboveFlatPerfectSupportedWaldhausen j')
    ((boundedAboveFlatCoefficientSupportedEvaluation_exact j).comp
      (boundedAboveFlatPerfectSupportedPullback_isExact (boundedAboveFlatCoefficientSupportSquare
        j j' f l h)))
    (boundedAboveFlatCoefficientSupportedSectionReindexIso j j' f l h).symm

/-- Every specified support square gives exact original joint section reindexing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:194"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_exact :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j').cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j').weq
      (boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h) where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatCoefficientSupportedEvaluation
    j') _
    ((boundedAboveFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).zero hx)
  cofibration g hg := (boundedAboveFlatCoefficientSupportedSectionWaldhausen_cof_iff j' _).mpr
    ((boundedAboveFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).cofibration g hg)
  weak g hg := (boundedAboveFlatCoefficientSupportedSectionWaldhausen_weq_iff j' _).mpr
    ((boundedAboveFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).weak g hg)
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedAboveFlatCoefficientSupportedEvaluation j')
    exact (boundedAboveFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).pushout hi
      hp
end Reindex

/-- Supported section Models retain their original classes and the one global zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:212"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionModel
    (j : U ⟶ space i) [IsOpenImmersion j] : WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatCoefficientSupportedSections j,
       waldhausen := boundedAboveFlatCoefficientSupportedSectionWaldhausen j }⟩

/-- Original supported reindexing is an exact, literally zero-preserving Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedSections.lean:218"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionModelMap
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      f) :
    boundedAboveFlatCoefficientSupportedSectionModel j ⟶
      boundedAboveFlatCoefficientSupportedSectionModel j' :=
  ⟨⟨boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h,
      boundedAboveFlatCoefficientSupportedSectionsMap_exact j j' f l h⟩,
    boundedAboveFlatCoefficientSupportedSectionsMap_sectionZero j j' f l h⟩

end AlgebraicGeometry.Scheme.Modules

