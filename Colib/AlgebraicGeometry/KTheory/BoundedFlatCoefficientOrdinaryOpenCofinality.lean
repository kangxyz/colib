/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenGrading
public import Colib.AlgebraicGeometry.KTheory.PerfectOrdinaryQcqsCofinality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySectionKComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenKRestriction
/-! # Original ordinary coefficient restriction cofinality

Actual ordinary evaluation equivalences and the literal relative restriction map transport
qcqs cofinality, without an auxiliary support parameter or an added degree-zero surjectivity.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- The same evaluation computes the original coarse relative-open bounded-flat groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:40"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
def boundedAboveFlatCoefficientOpenKEquiv (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientOpenWaldhausen f a).K n ≃*
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).K n :=
  boundedAboveFlatCoefficientEvaluationKEquiv (boundedAboveFlatCoefficientOpenWaldhausen f a)
    (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a))
    (boundedAboveFlatCoefficientSectionEquivalence (op Q, a))
    (boundedAboveFlatCoefficientOpenEvaluation_coarse_exact f a)
    (boundedAboveFlatCoefficientOpenEquivalence_inverse_exact f a) n

/-- The actual geometric evaluation square retains the original bounded-flat restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:50"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
theorem boundedAboveFlatCoefficientOpenRestriction_KComparison (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientOpenWaldhausen f a).K n) :
    boundedAboveFlatCoefficientSectionKEquiv (op P, a) n
        (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) n x) =
      boundedAboveFlatPerfectOpenKRestrict (schemeMap f a) n
        (boundedAboveFlatCoefficientOpenKEquiv f a n x) :=
  boundedAboveFlatCoefficientEvaluationKEquiv_natural
    (boundedAboveFlatCoefficientOpenWaldhausen f a)
    (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a))
    (boundedAboveFlatCoefficientSectionEquivalence (op Q, a))
    (boundedAboveFlatCoefficientOpenEvaluation_coarse_exact f a)
    (boundedAboveFlatCoefficientOpenEquivalence_inverse_exact f a)
    (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
    (RingedSpace.boundedAboveFlatPerfectWaldhausen (space (op P, a)).toRingedSpace)
    (boundedAboveFlatCoefficientSectionEquivalence (op P, a))
    (boundedAboveFlatCoefficientOriginalEvaluation_exact (op P, a))
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact (op P, a))
    (boundedAboveFlatCoefficientOpenRestriction_exact f a)
    (boundedAboveFlatPerfectOpenRestriction_exact (schemeMap f a))
    (boundedAboveFlatCoefficientOpenRestrictionEvaluationIso f a) n x

/-- Original native open evaluation followed by the genuine bounded-flat perfect comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:71"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
def boundedAboveFlatCoefficientFullOpenPerfectKEquiv (_f : P ⟶ Q)
    [CompactSpace P.left] (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).K n ≃*
      (RingedSpace.perfectComplexesWaldhausen (space (op P, a)).toRingedSpace).K n := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  exact (boundedAboveFlatCoefficientSectionKEquiv (op P, a) n).trans
    (RingedSpace.boundedAboveFlatPerfectKEquiv (space (op P, a)).toRingedSpace n)

omit [IsOpenImmersion f.left] in
/-- The perfect evaluation comparison retains the original evaluated object's K-zero class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:81"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
theorem boundedAboveFlatCoefficientFullOpenPerfectKEquiv_objectClass [CompactSpace P.left]
    (a : Under R) (S : BoundedAboveFlatCoefficientSections (op P, a)) :
    boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0
        ((boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S) =
      (RingedSpace.perfectComplexesWaldhausen (space (op P, a)).toRingedSpace).kZeroObjectClass
        ((boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a).obj S) := by
  change RingedSpace.boundedAboveFlatPerfectToPerfectKMap (space (op P, a)).toRingedSpace 0
    (boundedAboveFlatCoefficientSectionKEquiv (op P, a) 0
      ((boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S)) = _
  rw [boundedAboveFlatCoefficientSectionKEquiv_objectClass]
  exact KMap_kZeroObjectClass
    (RingedSpace.boundedAboveFlatPerfectInclusion_isExact (space (op P, a)).toRingedSpace) _

/-- Original coarse evaluation followed by the genuine relative-open perfect comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:94"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
def boundedAboveFlatCoefficientOpenPerfectKEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientOpenWaldhausen f a).K n ≃*
      (perfectOpenWeakWaldhausen (schemeMap f a)).K n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedAboveFlatCoefficientOpenKEquiv f a n).trans
    (boundedAboveFlatPerfectOpenKEquiv (schemeMap f a) n)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The unchanged original section restriction compares with the original perfect restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:104"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
theorem boundedAboveFlatCoefficientOpenRestriction_perfectKComparison (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientOpenWaldhausen f a).K n) :
    boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a n
        (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) n x) =
      perfectOpenKRestrict (schemeMap f a) n
        (boundedAboveFlatCoefficientOpenPerfectKEquiv f a n x) := by
  change RingedSpace.boundedAboveFlatPerfectToPerfectKMap (space (op P, a)).toRingedSpace n
    (boundedAboveFlatCoefficientSectionKEquiv (op P, a) n
      (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) n x)) =
    perfectOpenKRestrict (schemeMap f a) n
      (boundedAboveFlatPerfectOpenToPerfectOpenKMap (schemeMap f a) n
        (boundedAboveFlatCoefficientOpenKEquiv f a n x))
  rw [boundedAboveFlatCoefficientOpenRestriction_KComparison]
  exact (DFunLike.congr_fun
    (boundedAboveFlatPerfectOpenKRestrict_comparison (schemeMap f a) n)
    (boundedAboveFlatCoefficientOpenKEquiv f a n x)).symm

variable [QuasiSeparatedSpace Q.left]

/-- Global cofinality proves original native section restriction injective in every degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:124"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
theorem boundedAboveFlatCoefficientOpenRestriction_KMap_injective (a : Under R) (n : ℕ) :
    Function.Injective (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) n) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  intro x y hxy
  apply (boundedAboveFlatCoefficientOpenPerfectKEquiv f a n).injective
  apply qcqs_perfectOpenKRestrict_injective (schemeMap f a) n
  rw [← boundedAboveFlatCoefficientOpenRestriction_perfectKComparison f a n x,
    ← boundedAboveFlatCoefficientOpenRestriction_perfectKComparison f a n y, hxy]

/-- The original section restriction is injective on the honest K-zero endpoint. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:136"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
theorem boundedAboveFlatCoefficientOpenRestriction_KMap_zero_injective (a : Under R) :
    Function.Injective (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) 0) :=
  boundedAboveFlatCoefficientOpenRestriction_KMap_injective f a 0

/-- Global cofinality proves bijectivity of the same original restriction in positive degrees. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenCofinality.lean:141"
  "adaptation" "Original ordinary section cofinality via actual evaluation and restriction"]
theorem boundedAboveFlatCoefficientOpenRestriction_KMap_succ_bijective (a : Under R) (n : ℕ) :
    Function.Bijective (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) (n + 1)) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  refine ⟨boundedAboveFlatCoefficientOpenRestriction_KMap_injective f a (n + 1), ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (qcqs_perfectOpenKRestrict_succ_bijective (schemeMap f a) n).surjective
    (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a (n + 1) y)
  refine ⟨(boundedAboveFlatCoefficientOpenPerfectKEquiv f a (n + 1)).symm z, ?_⟩
  apply (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a (n + 1)).injective
  rw [boundedAboveFlatCoefficientOpenRestriction_perfectKComparison, MulEquiv.apply_symm_apply]
  exact hz

end AlgebraicGeometry.Scheme.Modules
