/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenGrading
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenImagePullback




/-! # Actual coefficient-natural supported quotient grading

Original compact ambient and localization schemes give the genuine pair-square quotient action.
The same strict supported coefficient maps define G and its identity change-of-weakness q. No
compactness of the auxiliary open, exact raw-perfect pullback, contraction or stability is assumed.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Coefficient base change preserves compactness of the open scheme. -/
local instance coefficientSupportedOpenCompact (a : Under R) : CompactSpace (space (op P, a)) :=
  compactSpace_space (op P, a)

/-- Coefficient base change preserves compactness of the ambient scheme. -/
local instance coefficientSupportedAmbientCompact (a : Under R) : CompactSpace (space (op Q, a)) :=
  compactSpace_space (op Q, a)

/-- Arbitrary original coefficient arrows act on the actual raw supported image quotients. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:162"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
def boundedAboveFlatCoefficientSupportedOpenImageMap {a b : Under R} (g : a ⟶ b) :
    BoundedAboveFlatCoefficientSupportedOpenImageQuotient f T a →+
      BoundedAboveFlatCoefficientSupportedOpenImageQuotient f T b :=
  perfectSupportedOpenImageQuotientPullback (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a) (schemeMap f b)
    (boundedAboveFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g).symm

/-- The proved quotient action computes every actual supported reindexed section grade. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:173"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
theorem boundedAboveFlatCoefficientSupportedOpenImageMap_value {a b : Under R} (g : a ⟶ b)
    (S : BoundedAboveFlatCoefficientSupportedOpenSections f T a) :
    boundedAboveFlatCoefficientSupportedOpenImageMap f T g
        ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).value S) =
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T b).value
        ((boundedAboveFlatCoefficientSupportedOpenMap f T g).obj S) := by
  change perfectSupportedOpenImageQuotientPullback (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a) (schemeMap f b)
    (boundedAboveFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g).symm
      ((perfectSupportedOpenDeficitGrading (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).value
          ((boundedAboveFlatPerfectSupportedInclusion
            (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).obj
            ((boundedAboveFlatCoefficientSupportedEvaluation
              (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).obj S))) = _
  have h₀ := perfectSupportedOpenImageQuotientPullback_boundedFlat_objectClass
    (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a) (schemeMap f b)
    (boundedAboveFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g).symm
    ((boundedAboveFlatCoefficientSupportedEvaluation
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).obj S)
  let e := (boundedAboveFlatPerfectSupportedInclusion
    (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι).mapIso
    ((boundedAboveFlatCoefficientSupportedSectionReindexIso
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
      (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
      (boundedAboveFlatCoefficientOpenSupportPairMap f T g).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T g))).app S)
  exact h₀.trans ((perfectSupportedOpenDeficitGrading (schemeMap f b)
    (boundedAboveFlatCoefficientSupportOpen Q T b)).weak e.inv
    ((perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι).weq_iso e.inv
      (show IsIso e.inv from inferInstance)))

/-- Original supported coefficient reindexing is exact for actual quotient-grade weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:213"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
theorem boundedAboveFlatCoefficientSupportedGradedOpenSectionsMap_exact {a b : Under R} (g : a ⟶
  b) :
    IsExact (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.cof
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.weq
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T b).coarseStructure.cof
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T b).coarseStructure.weq
      (boundedAboveFlatCoefficientSupportedOpenMap f T g) where
  zero := (boundedAboveFlatCoefficientSupportedOpenMap_fine_exact f T g).zero
  cofibration := (boundedAboveFlatCoefficientSupportedOpenMap_fine_exact f T g).cofibration
  weak {S V} _ h :=
    (boundedAboveFlatCoefficientSupportedOpenImageMap_value f T g S).symm.trans
      ((congrArg (boundedAboveFlatCoefficientSupportedOpenImageMap f T g) h).trans
        (boundedAboveFlatCoefficientSupportedOpenImageMap_value f T g V))
  pushout := (boundedAboveFlatCoefficientSupportedOpenMap_fine_exact f T g).pushout

/-- Actual graded coefficient reindexing retains the same supported joint zero literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:228"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
def boundedAboveFlatCoefficientSupportedGradedOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedGradedOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenModel f T b :=
  ⟨⟨boundedAboveFlatCoefficientSupportedOpenMap f T g,
      boundedAboveFlatCoefficientSupportedGradedOpenSectionsMap_exact f T g⟩,
    (boundedAboveFlatCoefficientSupportedFullOpenModelMap f T g).property⟩

/-- The actual G_Z coefficient Model diagram retains the original strict reindexing laws. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:236"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
def boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor : Under R ⥤ WideSubcategory
  preservesZero.{u + 1} where
  obj := boundedAboveFlatCoefficientSupportedGradedOpenModel f T
  map := boundedAboveFlatCoefficientSupportedGradedOpenModelMap f T
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact congrArg (fun m : boundedAboveFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a ↦ m.hom.toFunctor)
      ((boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).map_id a)
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact congrArg (fun m : boundedAboveFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T c ↦ m.hom.toFunctor)
      ((boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).map_comp g h)

/-- The actual q_Z identity change of weakness is natural for every coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:251"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
def boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation :
    boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T where
  app := boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change boundedAboveFlatCoefficientSupportedOpenMap f T g ⋙ 𝟭 _ =
      𝟭 _ ⋙ boundedAboveFlatCoefficientSupportedOpenMap f T g
    simp only [Functor.comp_id, Functor.id_comp]

/-- The original iterated-S prespectra of the actual supported graded native Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:262"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
def boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T ⋙ prespectrumFunctor

/-- The same q_Z Model transformation gives the original supported grading prespectrum map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:267"
  "adaptation" "Actual quotient pair action and strict coefficient-natural graded Model"]
def boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation :
    boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T :=
  Functor.whiskerRight
    (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T) prespectrumFunctor

end AlgebraicGeometry.Scheme.Modules
