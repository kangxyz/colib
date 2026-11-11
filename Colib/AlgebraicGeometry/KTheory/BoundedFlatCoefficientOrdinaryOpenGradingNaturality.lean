/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenGrading
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenImagePullback
/-! # Original ordinary quotient grading under coefficient reindexing -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
variable [CompactSpace P.left] [CompactSpace Q.left]

local instance coefficientOpenCompact (a : Under R) : CompactSpace (space (op P, a)) :=
  compactSpace_space (op P, a)

local instance coefficientAmbientCompact (a : Under R) : CompactSpace (space (op Q, a)) :=
  compactSpace_space (op Q, a)

/-- Arbitrary coefficient maps act on the unchanged actual raw-perfect image quotients. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:142"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
def boundedAboveFlatCoefficientOpenImageMap {a b : Under R} (g : a ⟶ b) :
    BoundedAboveFlatCoefficientOpenImageQuotient f a →+
      BoundedAboveFlatCoefficientOpenImageQuotient f b :=
  perfectOpenImageQuotientPullback (schemeMap f a) (schemeMap f b)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g)

/-- The quotient action computes exactly the grade of every original reindexed section. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:153"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
theorem boundedAboveFlatCoefficientOpenImageMap_value {a b : Under R} (g : a ⟶ b)
    (S : BoundedAboveFlatCoefficientSections (op P, a)) :
    boundedAboveFlatCoefficientOpenImageMap f g ((boundedAboveFlatCoefficientFullOpenGrading f
      a).value S) =
      (boundedAboveFlatCoefficientFullOpenGrading f b).value
        ((boundedAboveFlatCoefficientSectionsMap
          (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).obj S) := by
  change perfectOpenImageQuotientPullback (schemeMap f a) (schemeMap f b)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g)
      ((imageQuotientGrading (perfectOpenWeakWaldhausen (schemeMap f a))
        (perfectComplexesRestrictOpenImmersion (schemeMap f a))
        (perfectOpenRestrict_isExact (schemeMap f a))).value
          ((RingedSpace.boundedAboveFlatPerfectInclusion (space (op P, a)).toRingedSpace).obj
          ((boundedAboveFlatCoefficientOriginalEvaluation (op P, a)).obj S))) = _
  rw [perfectOpenImageQuotientPullback_boundedFlat_objectClass]
  let e := (RingedSpace.boundedAboveFlatPerfectInclusion (space (op P, b)).toRingedSpace).mapIso
    ((boundedAboveFlatCoefficientSectionReindexIso
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).app S)
  exact (perfectOpenDeficitGrading (schemeMap f b)).weak e.inv
    ((RingedSpace.perfectComplexesWaldhausen (space (op P, b)).toRingedSpace).weq_iso e.inv
      (show IsIso e.inv from inferInstance))

/-- Original coefficient reindexing is exact for actual grade-equality weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:179"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
theorem boundedAboveFlatCoefficientGradedOpenSectionsMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.cof
      (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.weq
      (boundedAboveFlatCoefficientFullOpenGrading f b).coarseStructure.cof
      (boundedAboveFlatCoefficientFullOpenGrading f b).coarseStructure.weq
      (boundedAboveFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)) where
  zero := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).zero
  cofibration := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).cofibration
  weak {S T} _ h :=
    (boundedAboveFlatCoefficientOpenImageMap_value f g S).symm.trans
      ((congrArg (boundedAboveFlatCoefficientOpenImageMap f g) h).trans
        (boundedAboveFlatCoefficientOpenImageMap_value f g T))
  pushout := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).pushout

/-- The same graded coefficient map retains the one joint global zero literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:197"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
def boundedAboveFlatCoefficientGradedOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientGradedOpenModel f a ⟶ boundedAboveFlatCoefficientGradedOpenModel f
      b :=
  ⟨⟨boundedAboveFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g),
    boundedAboveFlatCoefficientGradedOpenSectionsMap_exact f g⟩,
    boundedAboveFlatCoefficientSectionsMap_sectionZero
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)⟩

/-- The actual graded coefficient Model diagram has the same strict reindexing laws. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:205"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
def boundedAboveFlatCoefficientGradedOpenModelFunctor : Under R ⥤ WideSubcategory
  preservesZero.{u+1} where
  obj := boundedAboveFlatCoefficientGradedOpenModel f
  map := boundedAboveFlatCoefficientGradedOpenModelMap f
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_id (boundedAboveFlatCoefficientProjection R) (op P, a)
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R)
      (X := (op P, a)) (Y := (op P, b)) (Z := (op P, c))
      (𝟙 (op P), g) (𝟙 (op P), h)

/-- The original fine-to-graded changes of weakness commute with every coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:218"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
def boundedAboveFlatCoefficientOpenGradingModelTransformation :
    boundedAboveFlatCoefficientFullOpenModelFunctor f ⟶
      boundedAboveFlatCoefficientGradedOpenModelFunctor f where
  app := boundedAboveFlatCoefficientOpenGradingModelMap f
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change boundedAboveFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b))
      (𝟙 (op P), g) ⋙ 𝟭 _ = 𝟭 _ ⋙
        boundedAboveFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    simp only [Functor.comp_id, Functor.id_comp]

/-- Original iterated-S realization of the same actual graded global coefficient Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:230"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
def boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientGradedOpenModelFunctor f ⋙ prespectrumFunctor

/-- The unchanged Model change of weakness gives the actual global grading prespectrum map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:234"
  "adaptation" "Original actual ordinary quotient action and graded reindexing"]
def boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation :
    boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f ⟶
      boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f :=
  Functor.whiskerRight (boundedAboveFlatCoefficientOpenGradingModelTransformation f)
    prespectrumFunctor

end AlgebraicGeometry.Scheme.Modules
