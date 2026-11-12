/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedSectionWaldhausen
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullback

/-!
# Native coefficient Models with auxiliary closed support

For an original open arrow and an auxiliary open `T`, support on every native
ambient fiber is the complement of the actual inverse image of `T` under the
original projection. The open-side support is its actual inverse image under
the native open arrow. Thus it is precisely the original support intersected
with the original open. Relative acyclicity also retains the intersection of
the auxiliary support with the complement of the localization open.

The actual supported fine and coarse Models use the same original joint zero.
Coefficient reindexing and restriction are exact and preserve this zero
literally. The strict original index squares give the coefficient-natural
restriction. No supported quotient grading, cofinality, seed or telescope
statement is asserted by these Model constructions.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace HomologicalComplex
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
    boundedAboveFlatCoefficientSupportedSectionEquivalence

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

omit [IsOpenImmersion f.left] in
/-- The same supported restriction is exact for both original fine structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:55"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact (a : Under R) :
    IsExact
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedAboveFlatCoefficientSupportedOpenRestriction f T a) :=
  boundedAboveFlatCoefficientSupportedSectionsMap_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).left
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))

/-- Actual supported ambient coefficient change is exact for the fine structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:75"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedAmbientMap_fine_exact {a b : Under R} (g : a ⟶ b) :
    IsExact
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T b).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T b).ι).weq
      (boundedAboveFlatCoefficientSupportedAmbientMap T g) :=
  boundedAboveFlatCoefficientSupportedSectionsMap_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι (boundedAboveFlatCoefficientSupportOpen Q T
      b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedAboveFlatCoefficientSupportPairMap Q T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T g))

/-- Coarse supported weakness is detected by the actual original section restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:93"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenWaldhausen (a : Under R) :
    Structure (BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :=
  Structure.withInverseImageWeak (boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact f
    T a)

/-- The same native fine weak class is contained in the restriction-detected coarse class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:98"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenNested (a : Under R) :
    Fibration.NestedWeakEquivalences
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι) :=
  Structure.inverseImageWeakNested (boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact
    f T a)

omit [IsOpenImmersion f.left] in
/-- Original supported coarse-to-fine restriction preserves all Waldhausen structure. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:106"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedAboveFlatCoefficientSupportedOpenRestriction f T a) :=
  Structure.withInverseImageWeak_exact
    (boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact f T a)

omit [IsOpenImmersion f.left] in
/-- Original supported open-side coefficient change is exact for the fine structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:119"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedOpenMap_fine_exact {a b : Under R} (g : a ⟶ b) :
    IsExact
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι).weq
      (boundedAboveFlatCoefficientSupportedOpenMap f T g) :=
  boundedAboveFlatCoefficientSupportedSectionsMap_exact
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    (boundedAboveFlatCoefficientOpenSupportPairMap f T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T g))

private theorem inverseImageSquare_exact {C C' D D' : Type*}
    [Category* C] [Category* C'] [Category* D] [Category* D']
    {V : Structure C} {V' : Structure C'} {W : Structure D} {W' : Structure D'}
    {r : C ⥤ D} {r' : C' ⥤ D'} {S : C ⥤ C'} {J : D ⥤ D'}
    (hr : IsExact V.cof V.weq W.cof W.weq r)
    (hr' : IsExact V'.cof V'.weq W'.cof W'.weq r')
    (hS : IsExact V.cof V.weq V'.cof V'.weq S)
    (hJ : IsExact W.cof W.weq W'.cof W'.weq J) (h : S ⋙ r' = r ⋙ J) :
    IsExact (Structure.withInverseImageWeak hr).cof (Structure.withInverseImageWeak hr).weq
      (Structure.withInverseImageWeak hr').cof (Structure.withInverseImageWeak hr').weq S where
  zero := hS.zero
  cofibration := hS.cofibration
  pushout := hS.pushout
  weak g hg := by
    have hcomp := (Structure.withInverseImageWeak_exact hr).comp hJ
    rw [← h] at hcomp
    exact hcomp.weak g hg

omit [IsOpenImmersion f.left] in
/-- Coefficient exactness for the coarse structure follows from the same strict restriction square.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:158"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedAmbientMap_coarse_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T b).cof
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T b).weq
      (boundedAboveFlatCoefficientSupportedAmbientMap T g) :=
  inverseImageSquare_exact
    (boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact f T a)
    (boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact f T b)
    (boundedAboveFlatCoefficientSupportedAmbientMap_fine_exact T g)
    (boundedAboveFlatCoefficientSupportedOpenMap_fine_exact f T g)
    (boundedAboveFlatCoefficientSupportedOpenRestriction_square f T g)

/-- Actual fine ambient Models on the original auxiliary support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:172"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedAmbientModel (a : Under R) : WideSubcategory
  preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientSupportedSectionModel (i := (op Q, a))
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι

/-- Original coefficient reindexing is an exact, zero-preserving fine ambient Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:177"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedAmbientModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedAmbientModel T a ⟶
      boundedAboveFlatCoefficientSupportedAmbientModel T b :=
  boundedAboveFlatCoefficientSupportedSectionModelMap
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι (boundedAboveFlatCoefficientSupportOpen Q T
      b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedAboveFlatCoefficientSupportPairMap Q T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T g))

/-- The original fine ambient support Models form a strict coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:187"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedAmbientModelFunctor : Under R ⥤ WideSubcategory
  preservesZero.{u + 1} where
  obj := boundedAboveFlatCoefficientSupportedAmbientModel T
  map := boundedAboveFlatCoefficientSupportedAmbientModelMap T
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_id
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι
      (boundedAboveFlatCoefficientSupportPairMap Q T (𝟙 a)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T (𝟙 a)))
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_comp
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι (boundedAboveFlatCoefficientSupportOpen Q T
        b).ι
      (boundedAboveFlatCoefficientSupportOpen Q T c).ι
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedAboveFlatCoefficientSupportPairMap Q T g).left
      (boundedAboveFlatCoefficientSupportPairMap Q T h).left
      (boundedAboveFlatCoefficientSupportPairMap Q T (g ≫ h)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T g))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T h))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T (g ≫ h)))

/-- The actual fine native open Model retains the original intersection support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:211"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFullOpenModel (a : Under R) : WideSubcategory
  preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientSupportedSectionModel (i := (op P, a))
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι

/-- Original open-side coefficient maps preserve all fine structure and the shared joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:216"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFullOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T b :=
  boundedAboveFlatCoefficientSupportedSectionModelMap
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    (boundedAboveFlatCoefficientOpenSupportPairMap f T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T g))

/-- The fine supported native open Models form the strict coefficient diagram F_Z. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:227"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFullOpenModelFunctor : Under R ⥤ WideSubcategory
  preservesZero.{u + 1} where
  obj := boundedAboveFlatCoefficientSupportedFullOpenModel f T
  map := boundedAboveFlatCoefficientSupportedFullOpenModelMap f T
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_id
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
      (boundedAboveFlatCoefficientOpenSupportPairMap f T (𝟙 a)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T (𝟙 a)))
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_comp
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
      (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι
      (boundedAboveFlatCoefficientOpenSupportOpen f T c).ι
      (i := (op P, a)) (k := (op P, b)) (t := (op P, c))
      (𝟙 (op P), g) (𝟙 (op P), h)
      (boundedAboveFlatCoefficientOpenSupportPairMap f T g).left
      (boundedAboveFlatCoefficientOpenSupportPairMap f T h).left
      (boundedAboveFlatCoefficientOpenSupportPairMap f T (g ≫ h)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T g))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T h))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T (g ≫ h)))

/-- The actual supported coarse Model retains the original ambient sections and shared zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:252"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenModel (a : Under R) : WideSubcategory preservesZero.{u
  + 1} :=
  ⟨{ Obj := BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a,
       waldhausen := boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a }⟩

/-- Coarse coefficient change is the same original supported functor and preserves its zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:257"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedOpenModel f T b :=
  ⟨⟨boundedAboveFlatCoefficientSupportedAmbientMap T g,
      boundedAboveFlatCoefficientSupportedAmbientMap_coarse_exact f T g⟩,
    (boundedAboveFlatCoefficientSupportedAmbientModelMap T g).property⟩

/-- The coarse supported native ambient Models form the strict coefficient diagram C_Z. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:265"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenModelFunctor : Under R ⥤ WideSubcategory
  preservesZero.{u + 1} where
  obj := boundedAboveFlatCoefficientSupportedOpenModel f T
  map := boundedAboveFlatCoefficientSupportedOpenModelMap f T
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_id
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι
      (boundedAboveFlatCoefficientSupportPairMap Q T (𝟙 a)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T (𝟙 a)))
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_comp
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι (boundedAboveFlatCoefficientSupportOpen Q T
        b).ι
      (boundedAboveFlatCoefficientSupportOpen Q T c).ι
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedAboveFlatCoefficientSupportPairMap Q T g).left
      (boundedAboveFlatCoefficientSupportPairMap Q T h).left
      (boundedAboveFlatCoefficientSupportPairMap Q T (g ≫ h)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T g))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T h))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T (g ≫ h)))

/-- The same original supported restriction is a coarse-to-fine Model map r_Z. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:289"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a :=
  ⟨⟨boundedAboveFlatCoefficientSupportedOpenRestriction f T a,
      boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a⟩,
    boundedAboveFlatCoefficientSupportedSectionsMap_sectionZero
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).left
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))⟩

/-- The actual supported restriction is natural in the original coefficient Model diagrams. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:303"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation :
    boundedAboveFlatCoefficientSupportedOpenModelFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T where
  app := boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedOpenRestriction_square f T g

/-- The fine-to-coarse Model map preserves the supported category and original joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:312"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedAmbientModel T a ⟶
      boundedAboveFlatCoefficientSupportedOpenModel f T a :=
  ⟨⟨𝟭 (BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a),
      Fibration.changeWeak_exact (boundedAboveFlatCoefficientSupportedOpenNested f T a)⟩, rfl⟩

/-- Fine-to-coarse change of weakness is natural under every original coefficient map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:320"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation :
    boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⟶
      boundedAboveFlatCoefficientSupportedOpenModelFunctor f T where
  app := boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change boundedAboveFlatCoefficientSupportedAmbientMap T g ⋙ 𝟭 _ =
      𝟭 _ ⋙ boundedAboveFlatCoefficientSupportedAmbientMap T g
    simp only [Functor.comp_id, Functor.id_comp]

/-- Original iterated-S realization of the actual supported coarse coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:331"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSupportedOpenModelFunctor f T ⋙ prespectrumFunctor

/-- Original iterated-S realization of the actual supported fine open coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:335"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor : Under R ⥤
  LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor

/-- Actual supported native restriction on the same coefficient prespectrum diagrams. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:339"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation :
    boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T :=
  Functor.whiskerRight (boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    prespectrumFunctor

/-- The actual fine Model on the original intersection of the closed supports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:347"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFiberModel (a : Under R) : WideSubcategory
  preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientSupportedSectionModel (i := (op Q, a))
    (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι

/-- Every coefficient arrow gives exact, zero-preserving reindexing on the same closed fiber. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:352"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFiberModelMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedFiberModel f T a ⟶
      boundedAboveFlatCoefficientSupportedFiberModel f T b :=
  boundedAboveFlatCoefficientSupportedSectionModelMap
    (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
    (boundedAboveFlatCoefficientFiberSupportOpen f T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedAboveFlatCoefficientFiberSupportPairMap f T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientFiberSupportPairMap f T g))

/-- Actual closed fiber Models form a strict coefficient diagram with the same joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:363"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFiberModelFunctor : Under R ⥤ WideSubcategory
  preservesZero.{u + 1} where
  obj := boundedAboveFlatCoefficientSupportedFiberModel f T
  map := boundedAboveFlatCoefficientSupportedFiberModelMap f T
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_id
      (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
      (boundedAboveFlatCoefficientFiberSupportPairMap f T (𝟙 a)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientFiberSupportPairMap f T (𝟙 a)))
  map_comp {a b c} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedSectionsMap_comp
      (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
      (boundedAboveFlatCoefficientFiberSupportOpen f T b).ι
      (boundedAboveFlatCoefficientFiberSupportOpen f T c).ι
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedAboveFlatCoefficientFiberSupportPairMap f T g).left
      (boundedAboveFlatCoefficientFiberSupportPairMap f T h).left
      (boundedAboveFlatCoefficientFiberSupportPairMap f T (g ≫ h)).left
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientFiberSupportPairMap f T g))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientFiberSupportPairMap f T h))
      (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientFiberSupportPairMap f T (g ≫ h)))

private theorem restrictionWeak_iff {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (A : X.Opens)
    {K L : (boundedAboveFlatPerfectSupported A.ι).FullSubcategory} (p : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedWaldhausen (j ⁻¹ᵁ A).ι).weq
        ((boundedAboveFlatPerfectSupportedPullback (supportRestrictionPair j A)).map p) ↔
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j A).weq p := by
  let e := NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j) (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K.obj) (e.app L.obj) (e.hom.naturality p.hom).symm)).symm

-- Factor the comparison over the original joint indices before specializing a native fiber.
private theorem supportedSectionRestrictionWeak_iff {i k : Index R}
    (η : i ⟶ k) [IsOpenImmersion (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η)]
    (A : (space i).Opens) {S V : BoundedAboveFlatCoefficientSupportedSections A.ι} (p : S ⟶ V) :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η ⁻¹ᵁ A).ι).weq
      ((boundedAboveFlatCoefficientSupportedSectionsMap A.ι
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η ⁻¹ᵁ A).ι η
        (supportRestrictionPair (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).left
        (MorphismProperty.Arrow.w (supportRestrictionPair
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A))).map p) ↔
      (boundedAboveFlatPerfectSupportedOpenWaldhausen
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).weq
        ((boundedAboveFlatCoefficientSupportedEvaluation A.ι).map p) :=
  (boundedAboveFlatCoefficientSupportedSectionsMap_weq_iff A.ι
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η ⁻¹ᵁ A).ι η
    (supportRestrictionPair (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).left
    (MorphismProperty.Arrow.w (supportRestrictionPair
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η)
      A)) p).trans
    (restrictionWeak_iff (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A
      ((boundedAboveFlatCoefficientSupportedEvaluation A.ι).map p))
/-- Coarse section weakness is exactly the original geometric supported relative-open weak class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenModels.lean:419"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff (a : Under R)
    {S V : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a} (p : S ⟶ V) :
    (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq p ↔
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).weq
        ((boundedAboveFlatCoefficientSupportedEvaluation
          (i := (op Q, a)) (boundedAboveFlatCoefficientSupportOpen Q T a).ι).map p) := by
  let : IsOpenImmersion (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)) :=
    (show IsOpenImmersion (schemeMap f a) from inferInstance)
  exact (Structure.withInverseImageWeak_weq_iff
    (boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact f T a) p).trans
    (supportedSectionRestrictionWeak_iff
      (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
      (boundedAboveFlatCoefficientSupportOpen Q T a) p)

end AlgebraicGeometry.Scheme.Modules

