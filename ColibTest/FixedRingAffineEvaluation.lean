/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComparison

/-!
# Actual affine evaluation and its inverse

The actual lifted functor, chosen zeros, exact inverse, whole inverse tracks and every level are
instantiated.
-/
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.FixedRingAffineEvaluation
variable (R : CommRingCat.{u})

example : (boundedAboveFlatAffineEvaluationModelMap R).hom.toFunctor =
    boundedAboveFlatAffineOriginalEvaluation R ⋙ AsSmall.up :=
  by rfl

example : (boundedAboveFlatAffineEvaluationSmallEquivalence R).functor.obj
    (boundedAboveFlatAffineSectionWaldhausen R).zero =
      AsSmall.up.obj (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero :=
  boundedAboveFlatAffineEvaluationSmall_zero R

example : IsExact (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.cof
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.weq
    (boundedAboveFlatAffineSectionWaldhausen R).cof (boundedAboveFlatAffineSectionWaldhausen R).weq
    (boundedAboveFlatAffineEvaluationSmallEquivalence R).inverse :=
  boundedAboveFlatAffineEvaluationSmall_inverse_exact R

example : (boundedAboveFlatAffineEvaluationInverseModelMap R).hom.toFunctor.obj
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.zero =
      (boundedAboveFlatAffineSectionWaldhausen R).zero :=
  (boundedAboveFlatAffineEvaluationInverseModelMap R).property

example (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    (boundedAboveFlatAffineOriginalEvaluation R).obj
      (boundedAboveFlatAffinePullbackSection R x) ≅ x :=
  boundedAboveFlatAffineOriginalEvaluationPullbackSectionIso R x

example : LoopPrespectrum.Homotopy
    (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      prespectrumMap (boundedAboveFlatAffineEvaluationInverseModelMap R))
    (𝟙 (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R)) :=
  boundedAboveFlatAffineEvaluationLeftHomotopy R

example : LoopPrespectrum.Homotopy
    (prespectrumMap (boundedAboveFlatAffineEvaluationInverseModelMap R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))) :=
  boundedAboveFlatAffineEvaluationRightHomotopy R

example (n : ℕ) : ContinuousMap.HomotopyEquiv
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n)
    ((originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :=
  boundedAboveFlatAffineEvaluationLevelEquiv R n

example : ContinuousMap.HomotopyEquiv
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0)
    ((originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space 0) :=
  boundedAboveFlatAffineEvaluationLevelEquiv R 0

example (n : ℕ) (s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationLeftHomotopy R).level (n + 1)
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n
        ((boundedAboveFlatAffineEvaluationLeftHomotopy R).level n (s, x)) t :=
  (boundedAboveFlatAffineEvaluationLeftHomotopy R).comm n s x t

example : IsStableEquivalence (boundedAboveFlatAffineEvaluationPrespectrumMap R) :=
  boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R


example (n : ℕ) (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationLeftHomotopy R).level n (0, x) = (prespectrumMap
        (boundedAboveFlatAffineEvaluationInverseModelMap R)).map n
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map n x) :=
  (boundedAboveFlatAffineEvaluationLeftHomotopy R).at_zero n x

example (n : ℕ) (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationLeftHomotopy R).level n (1, x) = x :=
  (boundedAboveFlatAffineEvaluationLeftHomotopy R).at_one n x

example (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatAffineEvaluationLeftHomotopy R).level n (s,
        (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n) =
        (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n :=
  (boundedAboveFlatAffineEvaluationLeftHomotopy R).at_point n s

example (n : ℕ) (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec
    R).toRingedSpace)).space n) :
    (boundedAboveFlatAffineEvaluationRightHomotopy R).level n (0, x) =
        (boundedAboveFlatAffineEvaluationPrespectrumMap R).map n ((prespectrumMap
        (boundedAboveFlatAffineEvaluationInverseModelMap R)).map n x) :=
  (boundedAboveFlatAffineEvaluationRightHomotopy R).at_zero n x

example (n : ℕ) (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec
    R).toRingedSpace)).space n) :
    (boundedAboveFlatAffineEvaluationRightHomotopy R).level n (1, x) = x :=
  (boundedAboveFlatAffineEvaluationRightHomotopy R).at_one n x

example (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatAffineEvaluationRightHomotopy R).level n (s, (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).point n) =
        (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).point n
        :=
  (boundedAboveFlatAffineEvaluationRightHomotopy R).at_point n s

example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
    (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatAffineEvaluationRightHomotopy R).level (n + 1) (s, (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).structureMap n x t) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec
          R).toRingedSpace)).structureMap n ((boundedAboveFlatAffineEvaluationRightHomotopy
          R).level n (s, x)) t :=
  (boundedAboveFlatAffineEvaluationRightHomotopy R).comm n s x t

example (n : ℕ) : (boundedAboveFlatAffineEvaluationLevelEquiv R n).toFun =
    (boundedAboveFlatAffineEvaluationPrespectrumMap R).map n := rfl

example (n : ℕ) : (boundedAboveFlatAffineEvaluationLevelEquiv R n).invFun =
    (prespectrumMap (boundedAboveFlatAffineEvaluationInverseModelMap R)).map n := rfl

example : (boundedAboveFlatAffineEvaluationSmallEquivalence R).inverse =
    AsSmall.down ⋙ (boundedAboveFlatAffineSectionEquivalence R).inverse := rfl

example : (boundedAboveFlatAffineEvaluationInverseModelMap R).hom.toFunctor =
    CategoryTheory.rebaseFunctor
      (boundedAboveFlatAffineEvaluationSmallEquivalence R).inverse
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.zero
      (boundedAboveFlatAffineSectionWaldhausen R).zero
      (((boundedAboveFlatAffineEvaluationSmall_inverse_exact R).zero
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.isZero).iso
        (boundedAboveFlatAffineSectionWaldhausen R).isZero) := rfl

example (d : ℤ) : IsIso ((stableHomotopyFunctor (d : ℤ)).map
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)) :=
  boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R d

example : IsIso ((stableHomotopyFunctor ((-1) : ℤ)).map
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)) :=
  boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R (-1)

example : IsIso ((stableHomotopyFunctor (0 : ℤ)).map
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)) :=
  boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R 0

example : IsIso ((stableHomotopyFunctor (1 : ℤ)).map
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)) :=
  boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R 1

example (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffineEvaluationKEquiv R n a =
      ((boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmallKEquiv n).symm
        (KMap (boundedAboveFlatAffineEvaluationSmall_exact R) n a) :=
  boundedAboveFlatAffineEvaluationKEquiv_apply R n a

example (a : (boundedAboveFlatAffineSectionWaldhausen R).K 0) :
    boundedAboveFlatAffineEvaluationKEquiv R 0 a =
      ((boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmallKEquiv 0).symm
        (KMap (boundedAboveFlatAffineEvaluationSmall_exact R) 0 a) :=
  boundedAboveFlatAffineEvaluationKEquiv_apply R 0 a

example (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalZeroSpaceEquiv (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) n
        (boundedAboveFlatAffineEvaluationKEquiv R n a) =
      HomotopyGroup.map ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map 0)
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a) :=
  boundedAboveFlatAffineEvaluationKEquiv_zeroSpace R n a

example (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalKStableEquiv (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) n
        (Additive.ofMul (boundedAboveFlatAffineEvaluationKEquiv R n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (smallModelKStableEquiv (boundedAboveFlatAffineSectionModel R) n (Additive.ofMul a)) :=
  boundedAboveFlatAffineEvaluationKEquiv_stable R n a

example (a : (boundedAboveFlatAffineSectionWaldhausen R).K 0) :
    originalZeroSpaceEquiv (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) 0
        (boundedAboveFlatAffineEvaluationKEquiv R 0 a) =
      HomotopyGroup.map ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map 0)
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R 0 a) :=
  boundedAboveFlatAffineEvaluationKEquiv_zeroSpace R 0 a

example (a : (boundedAboveFlatAffineSectionWaldhausen R).K 0) :
    originalKStableEquiv (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) 0
        (Additive.ofMul (boundedAboveFlatAffineEvaluationKEquiv R 0 a)) =
      (stableHomotopyFunctor (0 : ℤ)).map (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (smallModelKStableEquiv (boundedAboveFlatAffineSectionModel R) 0 (Additive.ofMul a)) :=
  boundedAboveFlatAffineEvaluationKEquiv_stable R 0 a


end ColibTest.FixedRingAffineEvaluation
