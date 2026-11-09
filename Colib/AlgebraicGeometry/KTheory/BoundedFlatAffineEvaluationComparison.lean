/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionPrespectrum
public import Colib.KTheory.Waldhausen.Iterated.ExactModelComparison

/-!
# Actual affine section evaluation on native prespectra

The actual evaluation equivalence is followed by `AsSmall.equiv`. Its original forward
functor is retained, and its actual inverse is canonically rebased at the chosen zero.
This universe bridge is essential: the original section and geometric categories have
different hom universes. No raw mixed-universe evaluation K-map is used.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual section equivalence followed by the actual small-universe lift. -/
def boundedAboveFlatAffineEvaluationSmallEquivalence (R : CommRingCat.{u}) :
    BoundedAboveFlatAffineSections R ≌
      AsSmall.{0} (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory :=
  (boundedAboveFlatAffineSectionEquivalence R).trans AsSmall.equiv

/-- Exactness of the unchanged lifted evaluation. -/
theorem boundedAboveFlatAffineEvaluationSmall_exact (R : CommRingCat.{u}) :
    IsExact (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.weq
      (boundedAboveFlatAffineEvaluationSmallEquivalence R).functor :=
  (boundedAboveFlatAffineOriginalEvaluation_exact R).comp
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall_up_exact

/-- Exactness of the actual inverse, before its chosen-zero normalization. -/
theorem boundedAboveFlatAffineEvaluationSmall_inverse_exact (R : CommRingCat.{u}) :
    IsExact (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.weq
      (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatAffineEvaluationSmallEquivalence R).inverse :=
  (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall_down_exact.comp
    (boundedAboveFlatAffineSectionEquivalence_inverse_exact R)

/-- Literal zero preservation follows from the proved original evaluation-zero equality. -/
theorem boundedAboveFlatAffineEvaluationSmall_zero (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineEvaluationSmallEquivalence R).functor.obj
        (boundedAboveFlatAffineSectionWaldhausen R).zero =
      AsSmall.up.obj (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero :=
  congrArg AsSmall.up.obj (boundedAboveFlatAffineOriginalEvaluation_sectionZero R)

/-- The native strict model arrow is the actual lifted evaluation. -/
def boundedAboveFlatAffineEvaluationModelMap (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionModel R ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) :=
  ExactModelEquivalence.forward
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_exact R) (boundedAboveFlatAffineEvaluationSmall_zero R)

/-- The original forward spectrum map is retained in every subsequent comparison. -/
@[colib_tag "COL-0358",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionComparison.lean:72-92"
    "adaptation"
    "Actual lifted affine evaluation and its unchanged native model and prespectrum map"]
def boundedAboveFlatAffineEvaluationPrespectrumMap (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.obj R ⟶
      originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) :=
  prespectrumMap (boundedAboveFlatAffineEvaluationModelMap R)

/-- The actual inverse is canonically rebased, rather than replaced by a supplied model. -/
def boundedAboveFlatAffineEvaluationInverseModelMap (R : CommRingCat.{u}) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) ⟶
      boundedAboveFlatAffineSectionModel R :=
  ExactModelEquivalence.backward
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_inverse_exact R)

/-- The full left inverse track for actual lifted evaluation. -/
def boundedAboveFlatAffineEvaluationLeftHomotopy (R : CommRingCat.{u}) :=
  ExactModelEquivalence.leftHomotopy
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_exact R)
    (boundedAboveFlatAffineEvaluationSmall_inverse_exact R)
    (boundedAboveFlatAffineEvaluationSmall_zero R)

/-- The full right inverse track for the same canonically normalized inverse. -/
def boundedAboveFlatAffineEvaluationRightHomotopy (R : CommRingCat.{u}) :=
  ExactModelEquivalence.rightHomotopy
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_exact R)
    (boundedAboveFlatAffineEvaluationSmall_inverse_exact R)
    (boundedAboveFlatAffineEvaluationSmall_zero R)

/-- Actual evaluation has a homotopy inverse at every level, including the zeroth loop level. -/
@[colib_tag "COL-0358",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionSpectrumEquivalence.lean:66-77"
    "adaptation"
    "The same evaluation and its canonically zero-normalized inverse at every natural level"]
def boundedAboveFlatAffineEvaluationLevelEquiv (R : CommRingCat.{u}) (n : ℕ) :=
  ExactModelEquivalence.levelHomotopyEquiv
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_exact R)
    (boundedAboveFlatAffineEvaluationSmall_inverse_exact R)
    (boundedAboveFlatAffineEvaluationSmall_zero R) n

/-- The unchanged evaluation spectrum map is stable in every integer degree. -/
@[colib_tag "COL-0358",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionSpectrumEquivalence.lean:79-100"
    "adaptation"
    "The original evaluation map induces isomorphisms in every integer stable degree"]
theorem boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence
    (R : CommRingCat.{u}) :
    LoopPrespectrum.IsStableEquivalence (boundedAboveFlatAffineEvaluationPrespectrumMap R) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_exact R)
    (boundedAboveFlatAffineEvaluationSmall_inverse_exact R)
    (boundedAboveFlatAffineEvaluationSmall_zero R)

/-- The genuine all-degree evaluation K-equivalence, through the actual universe bridge. -/
def boundedAboveFlatAffineEvaluationKEquiv (R : CommRingCat.{u}) (n : ℕ) :
    (boundedAboveFlatAffineSectionWaldhausen R).K n ≃*
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).K n :=
  ExactModelEquivalence.originalTargetKEquiv
    (A := boundedAboveFlatAffineSectionModel R) _
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineEvaluationSmall_exact R)
    (boundedAboveFlatAffineEvaluationSmall_inverse_exact R) n

/-- The forward map is exactly the lifted evaluation K-map followed by AsSmall descent. -/
theorem boundedAboveFlatAffineEvaluationKEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffineEvaluationKEquiv R n a =
      ((boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmallKEquiv n).symm
        (KMap (boundedAboveFlatAffineEvaluationSmall_exact R) n a) :=
  ExactModelEquivalence.originalTargetKEquiv_apply
    (A := boundedAboveFlatAffineSectionModel R) _ _ _ _ n a

/-- The zero-space formula identifies the original forward map, also in degree zero. -/
@[colib_tag "COL-0358",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionComparison.lean:94-110"
    "adaptation"
    "The actual affine K-equivalence agrees with the unchanged evaluation zero-space map"]
theorem boundedAboveFlatAffineEvaluationKEquiv_zeroSpace (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalZeroSpaceEquiv (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) n
        (boundedAboveFlatAffineEvaluationKEquiv R n a) =
      HomotopyGroup.map ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map 0)
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a) :=
  ExactModelEquivalence.originalTargetKEquiv_zeroSpace
    (A := boundedAboveFlatAffineSectionModel R) _ _ _ _
    (boundedAboveFlatAffineEvaluationSmall_zero R) n a

/-- The stable formula retains the same forward map and the actual direct-small comparison. -/
@[colib_tag "COL-0358",
  colib_ref "quillen"
    "Quillen/Waldhausen/SConstruction/Iterated/ModelStableHomotopy.lean:66-76"
    "adaptation"
    "Actual exact-model K-to-stable naturality for the lifted fixed-ring evaluation map",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionComparison.lean:53-70"
    "ingredient"
    "The actual affine K-equivalence is the lifted K-map followed by small-model descent"]
theorem boundedAboveFlatAffineEvaluationKEquiv_stable (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalKStableEquiv (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) n
        (Additive.ofMul (boundedAboveFlatAffineEvaluationKEquiv R n a)) =
      (LoopPrespectrum.stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (smallModelKStableEquiv (boundedAboveFlatAffineSectionModel R) n (Additive.ofMul a)) :=
  ExactModelEquivalence.originalTargetKEquiv_stable
    (A := boundedAboveFlatAffineSectionModel R) _ _ _ _
    (boundedAboveFlatAffineEvaluationSmall_zero R) n a

end AlgebraicGeometry.Scheme.Modules
