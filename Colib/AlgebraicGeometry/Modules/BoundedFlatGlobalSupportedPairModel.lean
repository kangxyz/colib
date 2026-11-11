/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairReindex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback

/-! # The original supported global section maps and strict diagram

These interfaces retain native global sections, their literal reindexing and the inherited
Stacks-perfect geometric fibers. They introduce no replacement perfect-complex model.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

variable {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)

/-- The full evaluated reindexing iso is the original geometric pullback transition. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairModel.lean:23"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedPairReindexEvaluationIso :
    boundedAboveFlatGlobalSupportedEvaluation (X := Opposite.op B.right) B.hom ⋙
        boundedAboveFlatPerfectSupportedPullback g ≅
      boundedAboveFlatGlobalSupportedPairReindex g ⋙
        boundedAboveFlatGlobalSupportedEvaluation (X := Opposite.op A.right) A.hom :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported A.hom).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatGlobalSectionSupported (X := Opposite.op
      B.right) B.hom).ι
      (Functor.isoWhiskerRight (boundedAboveFlatGlobalEvaluationPullbackIso g.right)
        (boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι))

/-- The unchanged geometric exact pullback supplies exactness after original evaluation. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairModel.lean:34"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedPairReindex_evaluation_exact :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op B.right) B.hom).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op B.right) B.hom).weq
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).weq
      (boundedAboveFlatGlobalSupportedPairReindex g ⋙
        boundedAboveFlatGlobalSupportedEvaluation (X := Opposite.op A.right) A.hom) :=
  ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op B.right) B.hom)
    (boundedAboveFlatPerfectSupportedWaldhausen A.hom)
    ((boundedAboveFlatGlobalSupportedEvaluation_exact (X := Opposite.op B.right) B.hom).comp
      (boundedAboveFlatPerfectSupportedPullback_isExact g))
        (boundedAboveFlatGlobalSupportedPairReindexEvaluationIso g)

/-- Reindexing is exact for the actual supported structures transported by evaluation. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairModel.lean:48"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedPairReindex_exact :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op B.right) B.hom).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op B.right) B.hom).weq
      (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op A.right) A.hom).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X := Opposite.op A.right) A.hom).weq
      (boundedAboveFlatGlobalSupportedPairReindex g) := by
  let : (boundedAboveFlatGlobalSupportedEvaluation (X := Opposite.op A.right)
    A.hom).IsEquivalence :=
    boundedAboveFlatGlobalSupportedEvaluation_isEquivalence (X := Opposite.op A.right) A.hom
  exact {
  zero := fun hz => IsZero.of_full_of_faithful_of_isZero
    (boundedAboveFlatGlobalSupportedEvaluation (X := Opposite.op A.right) A.hom) _
    ((boundedAboveFlatGlobalSupportedPairReindex_evaluation_exact g).zero hz)
  cofibration := fun f hf => (boundedAboveFlatGlobalSupportedPairReindex_evaluation_exact
    g).cofibration f hf
  weak := fun f hf => (boundedAboveFlatGlobalSupportedPairReindex_evaluation_exact g).weak f hf
  pushout := fun hi hp => IsPushout.of_map_of_faithful
    (boundedAboveFlatGlobalSupportedEvaluation (X := Opposite.op A.right) A.hom)
    ((boundedAboveFlatGlobalSupportedPairReindex_evaluation_exact g).pushout hi hp) }

/-- The original supported section reindexing, with its literal original selected zero. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairModel.lean:67"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedPairModelMap :
    boundedAboveFlatGlobalSupportedSectionModel (X := Opposite.op B.right) B.hom ⟶
      boundedAboveFlatGlobalSupportedSectionModel (X := Opposite.op A.right) A.hom :=
  ⟨⟨boundedAboveFlatGlobalSupportedPairReindex g,
    boundedAboveFlatGlobalSupportedPairReindex_exact g⟩,
    boundedAboveFlatGlobalSupportedPairReindex_zero g⟩

/-- Forgetting support retains the original strict global Model square. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairModel.lean:75"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedPairModelMap_forget :
    boundedAboveFlatGlobalSupportedPairModelMap g ≫ boundedAboveFlatGlobalSupportedForget (X
      := Opposite.op A.right) A.hom =
      boundedAboveFlatGlobalSupportedForget (X := Opposite.op B.right) B.hom ≫
        boundedAboveFlatGlobalSectionModelFunctor.map g.right.op := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact boundedAboveFlatGlobalSupportedPairReindex_forget g

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

attribute [colib_tag "COL-0534"] boundedAboveFlatGlobalSupportedPairReindex_exact

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
