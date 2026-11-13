/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
public import Colib.CategoryTheory.ObjectProperty.NestedEquivalence
public import Colib.CategoryTheory.ObjectProperty.LiftComposition

/-!
# Actual supported sections on the joint geometric family

The original restricted acyclicity defines supported sections. Actual evaluation is an
equivalence, and every original commuting support square gives the literal reindexing functor,
its geometric comparison and its identity/composition laws.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {i k t : Index R} {U V W : Scheme.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- Actual support tests the original evaluated complex on the specified open. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:38"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSectionSupported (j : U ⟶ space i) [IsOpenImmersion j] :
    ObjectProperty (BoundedAboveFlatCoefficientSections i) := fun S ↦
  (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S).obj).Acyclic

/-- Supported objects retain the original native cocartesian sections. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:43"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
abbrev BoundedAboveFlatCoefficientSupportedSections (j : U ⟶ space i) [IsOpenImmersion j] :=
  (boundedAboveFlatCoefficientSectionSupported j).FullSubcategory

/-- Original identity evaluation retains the actual supported chain complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:47"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedEvaluation (j : U ⟶ space i) [IsOpenImmersion j] :
    BoundedAboveFlatCoefficientSupportedSections j ⥤ (boundedAboveFlatPerfectSupported
      j).FullSubcategory :=
  (boundedAboveFlatPerfectSupported j).lift
    ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙
      boundedAboveFlatCoefficientOriginalEvaluation i ⋙
      (boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι)
    (fun S ↦ ⟨((boundedAboveFlatCoefficientOriginalEvaluation i).obj S.obj).property, S.property⟩)

/-- Forgetting support after evaluation keeps the original chain complex literally. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:55"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedEvaluation_obj
    (j : U ⟶ space i) [IsOpenImmersion j] (S : BoundedAboveFlatCoefficientSupportedSections j) :
    ((boundedAboveFlatCoefficientSupportedEvaluation j).obj S).obj =
      ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S.obj).obj := rfl

/-- Support is exactly the inverse image of original geometric support under evaluation. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:61"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedEvaluation_property
    (j : U ⟶ space i) [IsOpenImmersion j] :
    ((boundedAboveFlatPerfectSupported j).inverseImage (boundedAboveFlatPerfectComplex (space
      i).toRingedSpace).ι).inverseImage
        (boundedAboveFlatCoefficientSectionEquivalence i).functor =
      boundedAboveFlatCoefficientSectionSupported j := by
  funext S
  apply propext
  exact and_iff_right ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S).property

/-- Supported coefficient evaluation is an equivalence on the actual supported subcategories. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:70"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
instance boundedAboveFlatCoefficientSupportedEvaluation_isEquivalence
    (j : U ⟶ space i) [IsOpenImmersion j] :
    (boundedAboveFlatCoefficientSupportedEvaluation j).IsEquivalence := by
  let := boundedAboveFlatPerfectSupported_closedUnderIsomorphisms j
  let e := CategoryTheory.ObjectProperty.evaluationRestrictionEquivalence.{u + 1, u, u + 1, u + 1}
    (boundedAboveFlatPerfectComplex (space i).toRingedSpace) (boundedAboveFlatPerfectSupported j)
      (fun _ h ↦ h.1)
    (boundedAboveFlatCoefficientSectionEquivalence i) (boundedAboveFlatCoefficientSectionSupported
      j)
    (boundedAboveFlatCoefficientSupportedEvaluation_property j)
  have he : e.functor = boundedAboveFlatCoefficientSupportedEvaluation j :=
    CategoryTheory.ObjectProperty.evaluationRestrictionEquivalence_functor
      (boundedAboveFlatPerfectComplex (space i).toRingedSpace) (boundedAboveFlatPerfectSupported
        j) (fun _ h ↦ h.1)
      (boundedAboveFlatCoefficientSectionEquivalence i)
        (boundedAboveFlatCoefficientSectionSupported j)
      (boundedAboveFlatCoefficientSupportedEvaluation_property j) _
  rw [← he]
  exact e.isEquivalence_functor

/-- The original supported evaluation is the literal forward functor of its genuine equivalence. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:86"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionEquivalence
    (j : U ⟶ space i) [IsOpenImmersion j] :
    BoundedAboveFlatCoefficientSupportedSections j ≌ (boundedAboveFlatPerfectSupported
      j).FullSubcategory :=
  (boundedAboveFlatCoefficientSupportedEvaluation j).asEquivalence

/-- The forward equivalence keeps the specified original supported evaluation literally. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:92"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionEquivalence_functor
    (j : U ⟶ space i) [IsOpenImmersion j] :
    (boundedAboveFlatCoefficientSupportedSectionEquivalence j).functor =
      boundedAboveFlatCoefficientSupportedEvaluation j := rfl

section Reindex
variable (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
  (f : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
include l h

/-- The specified original support square over the native joint map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:103"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportSquare :
    (MorphismProperty.Arrow.mk j' inferInstance :
      AlgebraicGeometry.Scheme.OpenPairs) ⟶
      MorphismProperty.Arrow.mk j inferInstance :=
  MorphismProperty.Arrow.homMk l (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) h

/-- Original joint reindexing preserves actual support on the specified support square. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:110"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSectionsMap_supported
    (S : BoundedAboveFlatCoefficientSections i) (hS : boundedAboveFlatCoefficientSectionSupported
      j S) :
    boundedAboveFlatCoefficientSectionSupported j' ((boundedAboveFlatCoefficientSectionsMap f).obj
      S) := by
  have hp := boundedAboveFlatPerfectSupported_pairPullback
    (boundedAboveFlatCoefficientSupportSquare j j' f l h)
    (K := ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S).obj)
    ⟨((boundedAboveFlatCoefficientOriginalEvaluation i).obj S).property, hS⟩
  intro n
  exact (hp.2 n).of_iso (((restrictFunctor j').mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    ((boundedAboveFlatPerfectComplex (space k).toRingedSpace).ι.mapIso
    ((boundedAboveFlatCoefficientSectionReindexIso f).app S))).symm

/-- The original reindexing restricted to its actual supported objects. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:122"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionsMap :
    BoundedAboveFlatCoefficientSupportedSections j ⥤ BoundedAboveFlatCoefficientSupportedSections
      j' :=
  (boundedAboveFlatCoefficientSectionSupported j').lift
    ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙ boundedAboveFlatCoefficientSectionsMap f)
    (fun S ↦ boundedAboveFlatCoefficientSectionsMap_supported j j' f l h S.obj S.property)

/-- Forgetting support keeps the original section reindexing on objects and morphisms. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:129"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_forget :
    boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        (boundedAboveFlatCoefficientSectionSupported j').ι =
      (boundedAboveFlatCoefficientSectionSupported j).ι ⋙ boundedAboveFlatCoefficientSectionsMap f
        := rfl

omit l h in
/-- Forgetting the actual supported evaluation retains the original complex-valued functor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:136"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedEvaluation_forget :
    boundedAboveFlatCoefficientSupportedEvaluation j ⋙ (boundedAboveFlatPerfectSupported j).ι =
      (boundedAboveFlatCoefficientSectionSupported j).ι ⋙
        boundedAboveFlatCoefficientOriginalEvaluation i ⋙
        (boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι :=
  CategoryTheory.ObjectProperty.lift_comp_ι (boundedAboveFlatPerfectSupported j)
    ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙
      boundedAboveFlatCoefficientOriginalEvaluation i ⋙
      (boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι)
    (fun S ↦ ⟨((boundedAboveFlatCoefficientOriginalEvaluation i).obj S.obj).property, S.property⟩)

section
attribute [local irreducible] boundedAboveFlatCoefficientSupportedSectionsMap
  boundedAboveFlatCoefficientSupportedEvaluation

/-- The original reindexed supported evaluation keeps its specified underlying functor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:150"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedReindexEvaluation_forget :
    (boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        boundedAboveFlatCoefficientSupportedEvaluation j') ⋙ (boundedAboveFlatPerfectSupported
          j').ι =
      (boundedAboveFlatCoefficientSectionSupported j).ι ⋙
        (boundedAboveFlatCoefficientSectionsMap f ⋙ boundedAboveFlatCoefficientOriginalEvaluation
          k) ⋙
          (boundedAboveFlatPerfectComplex (space k).toRingedSpace).ι :=
  CategoryTheory.ObjectProperty.comp_forget_eq
    (boundedAboveFlatCoefficientSectionSupported j) (boundedAboveFlatCoefficientSectionSupported j')
    (boundedAboveFlatPerfectSupported j') (boundedAboveFlatCoefficientSupportedSectionsMap j j' f
      l h)
    (boundedAboveFlatCoefficientSupportedEvaluation j') (boundedAboveFlatCoefficientSectionsMap f)
    (boundedAboveFlatCoefficientOriginalEvaluation k) (boundedAboveFlatPerfectComplex (space
      k).toRingedSpace).ι
    (boundedAboveFlatCoefficientSupportedSectionsMap_forget j j' f l h)
    (boundedAboveFlatCoefficientSupportedEvaluation_forget j')
end

/-- Actual geometric supported pullback keeps the original complex pullback literally. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:166"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedPairPullback_forget :
    boundedAboveFlatPerfectSupportedPullback (boundedAboveFlatCoefficientSupportSquare j j' f l h) ⋙
        (boundedAboveFlatPerfectSupported j').ι =
      (boundedAboveFlatPerfectSupported j).ι ⋙
        (pullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).mapHomologicalComplex
          (.up ℤ) :=
  CategoryTheory.ObjectProperty.lift_comp_ι (boundedAboveFlatPerfectSupported j')
    ((boundedAboveFlatPerfectSupported j).ι ⋙
      (pullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).mapHomologicalComplex
        (.up ℤ))
    (fun K ↦ boundedAboveFlatPerfectSupported_pairPullback
      (boundedAboveFlatCoefficientSupportSquare j j' f l h) K.property)

omit l h in
/-- The actual bounded-flat pullback keeps the original complex pullback literally. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:181"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientOriginalPullback_forget :
    boundedAboveFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) ⋙
        (boundedAboveFlatPerfectComplex (space k).toRingedSpace).ι =
      (boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι ⋙
        (pullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).mapHomologicalComplex
          (.up ℤ) :=
  CategoryTheory.ObjectProperty.lift_comp_ι (boundedAboveFlatPerfectComplex (space k).toRingedSpace)
    ((boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι ⋙
      (pullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).mapHomologicalComplex
        (.up ℤ))
    (fun K ↦ boundedAboveFlatPerfectComplex_pullback
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
      K.property)

section
attribute [local irreducible] boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatPerfectSupportedPullback boundedAboveFlatPerfectPullback

/-- The original evaluation and supported pullback retain their actual underlying composite. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:199"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedEvaluationPullback_forget :
    (boundedAboveFlatCoefficientSupportedEvaluation j ⋙
        boundedAboveFlatPerfectSupportedPullback (boundedAboveFlatCoefficientSupportSquare j j' f
          l h)) ⋙
        (boundedAboveFlatPerfectSupported j').ι =
      (boundedAboveFlatCoefficientSectionSupported j).ι ⋙
        (boundedAboveFlatCoefficientOriginalEvaluation i ⋙
          boundedAboveFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
            f)) ⋙
          (boundedAboveFlatPerfectComplex (space k).toRingedSpace).ι :=
  CategoryTheory.ObjectProperty.comp_forget_eq_of_comparison
    (boundedAboveFlatCoefficientSectionSupported j) (boundedAboveFlatPerfectSupported j)
    (boundedAboveFlatPerfectSupported j') (boundedAboveFlatCoefficientSupportedEvaluation j)
    (boundedAboveFlatPerfectSupportedPullback (boundedAboveFlatCoefficientSupportSquare j j' f l h))
    (boundedAboveFlatCoefficientOriginalEvaluation i) (boundedAboveFlatPerfectComplex (space
      i).toRingedSpace).ι
    ((pullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).mapHomologicalComplex
      (.up ℤ))
    (boundedAboveFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (boundedAboveFlatPerfectComplex (space k).toRingedSpace).ι
      (boundedAboveFlatCoefficientSupportedEvaluation_forget j)
    (boundedAboveFlatCoefficientSupportedPairPullback_forget j j' f l h)
    (boundedAboveFlatCoefficientOriginalPullback_forget f)

/-- The original transition is a supported natural isomorphism on the same complexes. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:220"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedSectionReindexIso :
    boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        boundedAboveFlatCoefficientSupportedEvaluation j' ≅
      boundedAboveFlatCoefficientSupportedEvaluation j ⋙
        boundedAboveFlatPerfectSupportedPullback (boundedAboveFlatCoefficientSupportSquare j j' f
          l h) :=
  CategoryTheory.ObjectProperty.isoOfForgetIso (boundedAboveFlatPerfectSupported j')
    (boundedAboveFlatCoefficientSupportedSectionsMap j j' f l h ⋙
      boundedAboveFlatCoefficientSupportedEvaluation j')
    (boundedAboveFlatCoefficientSupportedEvaluation j ⋙
      boundedAboveFlatPerfectSupportedPullback (boundedAboveFlatCoefficientSupportSquare j j' f l
        h))
    _ _ (boundedAboveFlatCoefficientSupportedReindexEvaluation_forget j j' f l h)
    (boundedAboveFlatCoefficientSupportedEvaluationPullback_forget j j' f l h)
    (Functor.isoWhiskerLeft (boundedAboveFlatCoefficientSectionSupported j).ι
      (Functor.isoWhiskerRight (boundedAboveFlatCoefficientSectionReindexIso f)
        (boundedAboveFlatPerfectComplex (space k).toRingedSpace).ι))
end

end Reindex

/-- Equal underlying functors give equal supported lifts. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:239"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem supported_lift_congr {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) : P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- Identity on the joint index is literal identity for every actual support square over it. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:246"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_id
    (j : U ⟶ space i) [IsOpenImmersion j] (l : U ⟶ U)
    (h : l ≫ j = j ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 i)) :
    boundedAboveFlatCoefficientSupportedSectionsMap j j (𝟙 i) l h =
      𝟭 (BoundedAboveFlatCoefficientSupportedSections j) := by
  change (boundedAboveFlatCoefficientSectionSupported j).lift
    ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙ boundedAboveFlatCoefficientSectionsMap (𝟙
      i)) _ =
      (boundedAboveFlatCoefficientSectionSupported j).lift
        (boundedAboveFlatCoefficientSectionSupported j).ι _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedAboveFlatCoefficientSectionSupported j).ι ⋙ F)
    (underCocartesianReindex_id (boundedAboveFlatCoefficientProjection R) i)

/-- Composition keeps the original reindexing; proof witnesses do not alter section maps. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:259"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_comp
    (j : U ⟶ space i) (j' : V ⟶ space k) (j'' : W ⟶ space t)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : i ⟶ k) (g : k ⟶ t) (l : V ⟶ U) (m : W ⟶ V) (n : W ⟶ U)
    (hf : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
    (hg : m ≫ j' = j'' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map g)
    (hfg : n ≫ j = j'' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (f ≫ g)) :
    boundedAboveFlatCoefficientSupportedSectionsMap j j'' (f ≫ g) n hfg =
      boundedAboveFlatCoefficientSupportedSectionsMap j j' f l hf ⋙
        boundedAboveFlatCoefficientSupportedSectionsMap j' j'' g m hg := by
  change (boundedAboveFlatCoefficientSectionSupported j'').lift
    ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙ boundedAboveFlatCoefficientSectionsMap (f
      ≫ g)) _ =
      (boundedAboveFlatCoefficientSectionSupported j'').lift
        ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙
          boundedAboveFlatCoefficientSectionsMap f ⋙
          boundedAboveFlatCoefficientSectionsMap g) _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedAboveFlatCoefficientSectionSupported j).ι ⋙ F)
    (underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R) f g)

/-- A strict square in the original joint index remains strict after imposing actual support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedSections.lean:279"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedSectionsMap_square
    {k' : Index R} {V' : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) (j₂ : V' ⟶ space k') (j₃ : W ⟶ space t)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (f : i ⟶ k) (g : k ⟶ t) (f' : i ⟶ k') (g' : k' ⟶ t)
    (l : V ⟶ U) (m : W ⟶ V) (l' : V' ⟶ U) (m' : W ⟶ V')
    (hf : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
    (hg : m ≫ j' = j₃ ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map g)
    (hf' : l' ≫ j = j₂ ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f')
    (hg' : m' ≫ j₂ = j₃ ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map g')
    (h : f ≫ g = f' ≫ g') :
    boundedAboveFlatCoefficientSupportedSectionsMap j j' f l hf ⋙
        boundedAboveFlatCoefficientSupportedSectionsMap j' j₃ g m hg =
      boundedAboveFlatCoefficientSupportedSectionsMap j j₂ f' l' hf' ⋙
        boundedAboveFlatCoefficientSupportedSectionsMap j₂ j₃ g' m' hg' := by
  change (boundedAboveFlatCoefficientSectionSupported j₃).lift
    ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙ boundedAboveFlatCoefficientSectionsMap f ⋙
      boundedAboveFlatCoefficientSectionsMap g) _ =
    (boundedAboveFlatCoefficientSectionSupported j₃).lift
      ((boundedAboveFlatCoefficientSectionSupported j).ι ⋙ boundedAboveFlatCoefficientSectionsMap
        f' ⋙
        boundedAboveFlatCoefficientSectionsMap g') _
  apply supported_lift_congr
  apply congrArg (fun F ↦ (boundedAboveFlatCoefficientSectionSupported j).ι ⋙ F)
  exact (underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R) f g).symm.trans
    ((congrArg (underCocartesianReindex (boundedAboveFlatCoefficientProjection R)) h).trans
      (underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R) f' g'))

end AlgebraicGeometry.Scheme.Modules
