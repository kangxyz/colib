/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedStructure
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
public import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationCoherence

/-! # Original global section reindexing on genuine open-pair squares -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckSections
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original section transition identifies geometric pullback with reindexed evaluation. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairReindex.lean:23"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalEvaluationPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y) ⋙ boundedAboveFlatPerfectPullback g ≅
      boundedAboveFlatGlobalSectionsMap g.op ⋙ boundedAboveFlatGlobalSectionEvaluation
        (Opposite.op X) :=
  originalEvaluationTransitionIso boundedAboveFlatPerfectPseudofunctor (Opposite.op Y)
      (Under.mk g.op) ≪≫
    eqToIso (originalEvaluation_reindex boundedAboveFlatPerfectPseudofunctor
      (Opposite.op Y) g.op).symm

/-- Every actual open-pair square preserves the evaluated support of original sections. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairReindex.lean:32"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalPairReindex_supported {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (S : BoundedAboveFlatGlobalSections (Opposite.op B.right))
    (hS : boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right) B.hom S) :
    boundedAboveFlatGlobalSectionSupported (X := Opposite.op A.right) A.hom
      ((boundedAboveFlatGlobalSectionsMap g.right.op).obj S) := by
  have hp := boundedAboveFlatPerfectSupported_pairPullback g
    (K := ((boundedAboveFlatGlobalSectionEvaluation (Opposite.op B.right)).obj S).obj)
    ⟨((boundedAboveFlatGlobalSectionEvaluation (Opposite.op B.right)).obj S).property, hS⟩
  let e := ((restrictFunctor A.hom).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    ((boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι.mapIso
      ((boundedAboveFlatGlobalEvaluationPullbackIso g.right).app S))
  intro n
  exact (hp.2 n).of_iso e

/-- Reindex the actual supported global sections without changing their underlying functor. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairReindex.lean:46"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def boundedAboveFlatGlobalSupportedPairReindex {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    (boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right) B.hom).FullSubcategory ⥤
      (boundedAboveFlatGlobalSectionSupported (X := Opposite.op A.right) A.hom).FullSubcategory :=
  (boundedAboveFlatGlobalSectionSupported (X := Opposite.op A.right) A.hom).lift
    ((boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right) B.hom).ι ⋙
      boundedAboveFlatGlobalSectionsMap g.right.op)
    (fun S => boundedAboveFlatGlobalPairReindex_supported g S.obj S.property)

/-- The entire forgetful square is literal equality. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairReindex.lean:55"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedPairReindex_forget {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    boundedAboveFlatGlobalSupportedPairReindex g ⋙
        (boundedAboveFlatGlobalSectionSupported (X := Opposite.op A.right) A.hom).ι =
      (boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right) B.hom).ι ⋙
        boundedAboveFlatGlobalSectionsMap g.right.op := rfl

/-- Reindexing retains the original selected section zero. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairReindex.lean:62"
  "adaptation" "The original maps, support predicates and proof on native section data."]
theorem boundedAboveFlatGlobalSupportedPairReindex_zero {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    (boundedAboveFlatGlobalSupportedPairReindex g).obj
        (boundedAboveFlatGlobalSupportedZero (X := Opposite.op B.right) B.hom) =
      boundedAboveFlatGlobalSupportedZero (X := Opposite.op A.right) A.hom := by
  apply ObjectProperty.FullSubcategory.ext
  exact boundedAboveFlatGlobalSectionsMap_zero g.right.op

end AlgebraicGeometry.Scheme.Modules
