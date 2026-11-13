/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedSectionWaldhausen
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOpenRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassSeed
public import Colib.CategoryTheory.ObjectProperty.LiftInclusion

/-! # Original ordinary supported coefficient diagram and exact support inclusion

These declarations keep the supported sections on the complement of the specified actual open.
The native evaluation, original joint zero and exact inclusion are unchanged. This file supplies
neither the coarse localization cone nor its stability; those remain later original declarations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Topology Topology.LoopPrespectrum HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
    boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- The original fine supported Model, retaining the restricted joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:53"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedModel (a : Under R) : WideSubcategory preservesZero.{u +
  1} :=
  boundedAboveFlatCoefficientSupportedSectionModel (schemeMap f a)

/-- The original coefficient arrow restricted to precisely the actual closed support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:57"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedModel f a ⟶ boundedAboveFlatCoefficientSupportedModel f b :=
  boundedAboveFlatCoefficientSupportedSectionModelMap (schemeMap f a) (schemeMap f b)
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g)

/-- Actual supported Models form the strict original native coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:66"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedModelFunctor : Under R ⥤ WideSubcategory preservesZero.{u
  + 1} where
  obj := boundedAboveFlatCoefficientSupportedModel f
  map := boundedAboveFlatCoefficientSupportedModelMap f
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_id (schemeMap f a)
      (boundedAboveFlatCoefficientOpenPairMap f (𝟙 a)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f (𝟙 a)))
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_comp
      (schemeMap f a) (schemeMap f b) (schemeMap f c)
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedAboveFlatCoefficientOpenPairMap f g).left
      (boundedAboveFlatCoefficientOpenPairMap f h).left
      (boundedAboveFlatCoefficientOpenPairMap f (g ≫ h)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f g))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f h))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f (g ≫ h)))

/-- Forgetting support after evaluation keeps the original bounded-flat complex literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:88"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
theorem boundedAboveFlatCoefficientSupportedEvaluation_forget_to_boundedAboveFlat (a : Under R) :
    boundedAboveFlatCoefficientSupportedEvaluation (schemeMap f a) ⋙ ObjectProperty.ιOfLE
        (show boundedAboveFlatPerfectSupported (schemeMap f a) ≤
          boundedAboveFlatPerfectComplex (space (op Q, a)).toRingedSpace
          from fun _ h ↦ h.1) =
      (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedAboveFlatCoefficientOriginalEvaluation (op Q, a) := by
  unfold boundedAboveFlatCoefficientSupportedEvaluation
  exact CategoryTheory.ObjectProperty.lift_comp_ιOfLE_comp
    (boundedAboveFlatPerfectSupported (schemeMap f a))
    (boundedAboveFlatPerfectComplex (space (op Q, a)).toRingedSpace)
    (fun _ h ↦ h.1) (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a))
    (fun S ↦ ⟨((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).property,
      S.property⟩)

/-- The original support inclusion is exact after its unchanged geometric evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:103"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
theorem boundedAboveFlatCoefficientSupportedForget_evaluation_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).weq
      ((boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)) := by
  rw [← boundedAboveFlatCoefficientSupportedEvaluation_forget_to_boundedAboveFlat f a]
  let := boundedAboveFlatPerfectComplex_containsZero
    (X := (space (op Q, a)).toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderIsomorphisms
    (X := (space (op Q, a)).toRingedSpace)
  let : (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex (space (op Q, a)).Modules ℤ)).IsExtensionClosed
        (boundedAboveFlatPerfectComplex (space (op Q, a)).toRingedSpace) :=
    boundedAboveFlatPerfectComplex_extensionClosed (X := (space (op Q, a)).toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderFiniteProducts
    (X := (space (op Q, a)).toRingedSpace)
  exact (boundedAboveFlatCoefficientSupportedEvaluation_exact (schemeMap f a)).comp
    (subcategoryInclusion_exact (A := (space (op Q, a)).Modules)
      (boundedAboveFlatPerfectSupported (schemeMap f a))
      (boundedAboveFlatPerfectComplex (space (op Q, a)).toRingedSpace) (fun _ h ↦ h.1))

/-- The actual supported inclusion preserves zero, both morphism classes and pushouts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:115"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
theorem boundedAboveFlatCoefficientSupportedForget_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι where
  zero hx := by
    let := boundedAboveFlatCoefficientOriginalEvaluation_isEquivalence (op Q, a)
    exact IsZero.of_full_of_faithful_of_isZero
      (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)) _
      ((boundedAboveFlatCoefficientSupportedForget_evaluation_exact f a).zero hx)
  cofibration p hp := (boundedAboveFlatCoefficientSupportedForget_evaluation_exact f
    a).cofibration p hp
  weak p hp := (boundedAboveFlatCoefficientSupportedForget_evaluation_exact f a).weak p hp
  pushout hi hp := by
    let := boundedAboveFlatCoefficientOriginalEvaluation_isEquivalence (op Q, a)
    apply IsPushout.of_map_of_faithful (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a))
    exact (boundedAboveFlatCoefficientSupportedForget_evaluation_exact f a).pushout hi hp

/-- The original support inclusion is a literal joint-zero-preserving Model arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:134"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedForgetModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedModel f a ⟶ boundedAboveFlatCoefficientSectionModel (op Q,
      a) :=
  ⟨⟨(boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι,
    boundedAboveFlatCoefficientSupportedForget_exact f a⟩, rfl⟩

/-- Original support inclusion is natural under the actual coefficient reindexing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:141"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedForgetModelTransformation :
    boundedAboveFlatCoefficientSupportedModelFunctor f ⟶
      boundedAboveFlatCoefficientSectionModelRow Q where
  app := boundedAboveFlatCoefficientSupportedForgetModelMap f
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_forget (schemeMap f a) (schemeMap f b)
      (𝟙 (op Q), g) (boundedAboveFlatCoefficientOpenPairMap f g).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f g))

/-- Original iterated-S realization of the actual supported native Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:156"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSupportedModelFunctor f ⋙ prespectrumFunctor

/-- Realize precisely the original supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:160"
  "adaptation" "Original ordinary supported coefficient diagram and exact inclusion."]
def boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation :
    boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⟶
      boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q :=
  Functor.whiskerRight (boundedAboveFlatCoefficientSupportedForgetModelTransformation f)
    prespectrumFunctor

end AlgebraicGeometry.Scheme.Modules
