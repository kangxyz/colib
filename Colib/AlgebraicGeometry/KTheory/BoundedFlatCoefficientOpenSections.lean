/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOpenRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionPrespectrum
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenRestrictionExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeakEquivalence




/-!
# Global native open coefficient Models

An actual open arrow of schemes over `Spec R` gives the native ambient and open
rows of the joint section diagram. The ambient coarse structure is the inverse
image of the original relative-open weak class under original identity
evaluation. The actual section restriction is exact into the fine native open
row and preserves the one joint zero literally.

Every coefficient arrow uses the original joint reindexing. The actual native
open square proves coarse exactness, and strict section reindexing proves the
restriction square. No compactness, flatness or affine-scheme hypothesis is
needed for these Models or their prespectra.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- Fine original evaluation is exact into the actual relative-open fiber. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:46"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatCoefficientOpenEvaluation_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).weq
      (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)) :=
  (boundedAboveFlatCoefficientOriginalEvaluation_exact (op Q, a)).changeWeakTarget
    (boundedAboveFlatPerfectOpenNested (schemeMap f a))

/-- Original relative-open weakness on the unchanged ambient sections and joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:56"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenWaldhausen (a : Under R) :
    Structure (BoundedAboveFlatCoefficientSections (op Q, a)) :=
  Structure.withInverseImageWeak (boundedAboveFlatCoefficientOpenEvaluation_exact f a)

/-- The unchanged fine ambient weak class is contained in this actual coarse class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:61"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenNested (a : Under R) :
    Fibration.NestedWeakEquivalences (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)) :=
  Structure.inverseImageWeakNested (boundedAboveFlatCoefficientOpenEvaluation_exact f a)

/-- Coarse original evaluation preserves precisely the original relative-open weak maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:66"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatCoefficientOpenEvaluation_coarse_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).weq
      (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)) :=
  Structure.withInverseImageWeak_exact (boundedAboveFlatCoefficientOpenEvaluation_exact f a)

/-- The actual inverse of original evaluation is exact for the same coarse structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:75"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatCoefficientOpenEquivalence_inverse_exact (a : Under R) :
    IsExact (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).weq
      (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (boundedAboveFlatCoefficientSectionEquivalence (op Q, a)).inverse :=
  Structure.withInverseImageWeak_inverse_exact
    (boundedAboveFlatCoefficientSectionEquivalence (op Q, a))
    (boundedAboveFlatCoefficientOriginalEvaluation_exact (op Q, a))
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))
    (boundedAboveFlatPerfectOpenNested (schemeMap f a))

/-- Coarse restriction followed by native fine evaluation is genuinely exact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:88"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatCoefficientOpenRestriction_evaluation_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (boundedAboveFlatPerfectWaldhausen (space (op P, a)).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (space (op P, a)).toRingedSpace).weq
      (boundedAboveFlatCoefficientOpenRestriction f a ⋙
        boundedAboveFlatCoefficientOriginalEvaluation (op P, a)) :=
  ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatCoefficientOpenWaldhausen f a) (boundedAboveFlatPerfectWaldhausen (space (op
      P, a)).toRingedSpace)
    ((boundedAboveFlatCoefficientOpenEvaluation_coarse_exact f a).comp
      (boundedAboveFlatPerfectOpenRestriction_exact (schemeMap f a)))
    (boundedAboveFlatCoefficientOpenRestrictionEvaluationIso f a).symm

/-- The same original restriction preserves zero, cofibrations, weak maps and pushouts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:102"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatCoefficientOpenRestriction_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).cof
      (boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).weq
      (boundedAboveFlatCoefficientOpenRestriction f a) where
  zero := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)).zero
  cofibration := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)).cofibration
  weak g hg := (boundedAboveFlatCoefficientOpenRestriction_evaluation_exact f a).weak g hg
  pushout := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)).pushout

/-- The original coefficient reindexing is exact for the coarse native ambient structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:117"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatCoefficientOpenSectionsMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (boundedAboveFlatCoefficientOpenWaldhausen f b).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f b).weq
      (boundedAboveFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)) where
  zero := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).zero
  cofibration := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).cofibration
  pushout := (boundedAboveFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).pushout
  weak k hk := by
    exact (ExtensionCategory.isExact_of_natIso
      (boundedAboveFlatCoefficientOpenWaldhausen f a)
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f b))
      ((boundedAboveFlatCoefficientOpenEvaluation_coarse_exact f a).comp
        (boundedAboveFlatPerfectOpenPullback_isExact (boundedAboveFlatCoefficientOpenPairMap f g)))
      (boundedAboveFlatCoefficientSectionReindexIso
        (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).symm).weak k hk

/-- The actual coarse Model on native ambient sections retains the joint global zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:139"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenModel (a : Under R) : WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatCoefficientSections (op Q, a),
     waldhausen := boundedAboveFlatCoefficientOpenWaldhausen f a }⟩

/-- Every original coefficient map is exact and literally zero-preserving for this coarse Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:143"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientOpenModel f a ⟶ boundedAboveFlatCoefficientOpenModel f b :=
  ⟨⟨ boundedAboveFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g),
     boundedAboveFlatCoefficientOpenSectionsMap_exact f g⟩,
     boundedAboveFlatCoefficientSectionsMap_sectionZero
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)⟩

/-- The global coarse coefficient diagram, with strict original identity and composition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:151"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenModelFunctor : Under R ⥤ WideSubcategory preservesZero.{u + 1}
  where
  obj := boundedAboveFlatCoefficientOpenModel f
  map := boundedAboveFlatCoefficientOpenModelMap f
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_id (boundedAboveFlatCoefficientProjection R) (op Q, a)
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R)
      (X := (op Q, a)) (Y := (op Q, b)) (Z := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)

/-- The actual native fine open row of the same joint Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:164"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientFullOpenModelFunctor (_f : P ⟶ Q) : Under R ⥤ WideSubcategory
  preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientSectionModelRow P

/-- Coarse-to-fine restriction uses the unchanged original joint reindexing and its literal zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:168"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenRestrictionModelMap (a : Under R) :
    boundedAboveFlatCoefficientOpenModel f a ⟶ (boundedAboveFlatCoefficientFullOpenModelFunctor
      f).obj a :=
  ⟨⟨ boundedAboveFlatCoefficientOpenRestriction f a,
     boundedAboveFlatCoefficientOpenRestriction_exact f a⟩,
     boundedAboveFlatCoefficientSectionsMap_sectionZero
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)⟩

/-- Coefficient change commutes literally with the actual native section restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:176"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenRestrictionModelTransformation :
    boundedAboveFlatCoefficientOpenModelFunctor f ⟶
      boundedAboveFlatCoefficientFullOpenModelFunctor f where
  app := boundedAboveFlatCoefficientOpenRestrictionModelMap f
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change underCocartesianReindex (boundedAboveFlatCoefficientProjection R)
        (X := (op Q, a)) (Y := (op Q, b)) (𝟙 (op Q), g) ⋙
      underCocartesianReindex (boundedAboveFlatCoefficientProjection R)
        (X := (op Q, b)) (Y := (op P, b)) (f.op, 𝟙 b) =
      underCocartesianReindex (boundedAboveFlatCoefficientProjection R)
        (X := (op Q, a)) (Y := (op P, a)) (f.op, 𝟙 a) ⋙
      underCocartesianReindex (boundedAboveFlatCoefficientProjection R)
        (X := (op P, a)) (Y := (op P, b)) (𝟙 (op P), g)
    rw [← underCocartesianReindex_comp, ← underCocartesianReindex_comp]
    exact congrArg (underCocartesianReindex (boundedAboveFlatCoefficientProjection R))
      ((rowTransformation f).naturality g)

/-- The unchanged ambient fine-to-coarse Model map changes only the weak class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:194"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenChangeWeakModelMap (a : Under R) :
    (boundedAboveFlatCoefficientSectionModelRow Q).obj a ⟶ boundedAboveFlatCoefficientOpenModel f
      a :=
  ⟨⟨ 𝟭 (BoundedAboveFlatCoefficientSections (op Q, a)),
     Fibration.changeWeak_exact (boundedAboveFlatCoefficientOpenNested f a)⟩,
     rfl⟩

/-- The same fine-to-coarse maps are natural in every original coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:201"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenChangeWeakModelTransformation :
    boundedAboveFlatCoefficientSectionModelRow Q ⟶ boundedAboveFlatCoefficientOpenModelFunctor f
      where
  app := boundedAboveFlatCoefficientOpenChangeWeakModelMap f
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change boundedAboveFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b))
      (𝟙 (op Q), g) ⋙ 𝟭 _ = 𝟭 _ ⋙
        boundedAboveFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    simp only [Functor.comp_id, Functor.id_comp]

/-- Original iterated-S realization of the actual global coarse Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:212"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientOpenModelFunctor f ⋙ prespectrumFunctor

/-- Original iterated-S realization of the fine native open row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:216"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientFullOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientFullOpenModelFunctor f ⋙ prespectrumFunctor

/-- The actual restriction transformation on the same global coefficient prespectra. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSections.lean:220"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
def boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation :
    boundedAboveFlatCoefficientOpenPrespectrumFunctor f ⟶
      boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f :=
  Functor.whiskerRight (boundedAboveFlatCoefficientOpenRestrictionModelTransformation f)
    prespectrumFunctor

end AlgebraicGeometry.Scheme.Modules
