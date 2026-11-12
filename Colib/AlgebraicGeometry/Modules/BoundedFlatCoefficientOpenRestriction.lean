/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback

/-!
# Actual restriction on joint coefficient sections

The original scheme-over-base open map gives the specified native open pair, coefficient
square, actual section restriction and original evaluation comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- The specified native open pair at the actual coefficient algebra. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientOpenRestriction.lean:32"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientOpenPair (a : Under R) : AlgebraicGeometry.Scheme.OpenPairs.{u} :=
  MorphismProperty.Arrow.mk (schemeMap f a) inferInstance

omit [IsOpenImmersion f.left] in
/-- Original coefficient maps commute with the actual native open inclusion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientOpenRestriction.lean:37"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientOpenSquare {a b : Under R} (g : a ⟶ b) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g) ≫ schemeMap f a =
      schemeMap f b ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g) := by
  change AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op P, a)) (k := (op P, b)) (𝟙
    (op P), g) ≫
      AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, a)) (k := (op P, a)) (f.op,
        𝟙 a) =
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, b)) (k := (op P, b)) (f.op, 𝟙
      b) ≫
      AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op
        Q), g)
  rw [← AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_comp,
    ← AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_comp]
  congr 1

/-- The genuine coefficient square between the same native open pairs. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientOpenRestriction.lean:55"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientOpenPairMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientOpenPair f b ⟶ boundedAboveFlatCoefficientOpenPair f a :=
  MorphismProperty.Arrow.homMk
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op P, a)) (k := (op P, b)) (𝟙 (op
      P), g))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op
      Q), g))
    (boundedAboveFlatCoefficientOpenSquare f g)

/-- The actual restriction is the joint coslice reindexing, with its unchanged functor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientOpenRestriction.lean:65"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientOpenRestriction (a : Under R) :
    BoundedAboveFlatCoefficientSections (op Q, a) ⥤ BoundedAboveFlatCoefficientSections (op P, a) :=
  boundedAboveFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)

/-- Original native evaluation compares restriction with the actual geometric pullback. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientOpenRestriction.lean:70"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientOpenRestrictionEvaluationIso (a : Under R) :
    boundedAboveFlatCoefficientOpenRestriction f a ⋙
        boundedAboveFlatCoefficientOriginalEvaluation (op P, a) ≅
      boundedAboveFlatCoefficientOriginalEvaluation (op Q, a) ⋙
        boundedAboveFlatPerfectPullback (schemeMap f a) :=
  boundedAboveFlatCoefficientSectionReindexIso (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)

end AlgebraicGeometry.Scheme.Modules
