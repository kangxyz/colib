/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Colib.KTheory.Waldhausen.GrothendieckComparison.ImageQuotientConeZero

/-!
Regressions for the actual image-quotient cone, the reversed original zero-to-image family,
endpoint-only transport, the unshifted target and precisely the original factorization premise.
No stable equivalence of this cone map in arbitrary signed degree is asserted.
-/

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.AlgebraicGrothendieck

universe u v

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

-- The source is the same canonically normalized exact functor, not a replacement model.
example : imageQuotientNormalizedFunctor W F hF =
    CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero) := rfl

example (A : C) : (imageQuotientZeroToNormalized W F hF).app A =
    V.isZero.to_ ((imageQuotientNormalizedFunctor W F hF).obj A) := rfl

example (A : C) : (imageQuotientGrading W F hF).coarseStructure.weq
    ((imageQuotientZeroToNormalized W F hF).app A) :=
  imageQuotientZeroToNormalized_weak W F hF A

-- A literal type ascription checks the cone source and the unshifted target.
example : mappingCone (exactOriginalPrespectrumMap W V hF) ⟶
    originalPrespectrum (imageQuotientGrading W F hF).coarseStructure :=
  imageQuotientConeMap W F hF

example : mappingConeInclusion (exactOriginalPrespectrumMap W V hF) ≫
    imageQuotientConeMap W F hF =
      Fibration.changeWeakPrespectrumMap (imageQuotientGrading W F hF).nested :=
  imageQuotientConeMap_inclusion W F hF

-- Every cylinder point, not only its two endpoints, retains the specified original null track.
example (n : ℕ) (s : unitInterval) (x : (originalPrespectrum W).space n) :
    (imageQuotientConeMap W F hF).map n
        (ReducedMappingCone.cylinder ((originalPrespectrum W).point n)
          ((originalPrespectrum V).point n) ((exactOriginalPrespectrumMap W V hF).map n)
          (s, x)) =
      (imageQuotientPrespectrumNullhomotopy W F hF).level n (s, x) := rfl

-- The source zero-to-image transformation is reversed at every time, with no new family.
example (n : ℕ) (s : unitInterval) (x : (originalPrespectrum W).space n) :
    (imageQuotientPrespectrumNullhomotopy W F hF).level n (s, x) =
      (originalPrespectrumTransformationHomotopy W
        (imageQuotientGrading W F hF).coarseStructure
        (zeroFunctor_isExact W (imageQuotientGrading W F hF).coarseStructure)
        (hF.rebase.comp
          (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested))
        rfl (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        (imageQuotientZeroToNormalized W F hF)
        (imageQuotientZeroToNormalized_weak W F hF)).level n (unitInterval.symm s, x) := rfl

example (n : ℕ) (x : (originalPrespectrum W).space n) :
    (imageQuotientPrespectrumNullhomotopy W F hF).level n (0, x) =
      (Fibration.changeWeakPrespectrumMap (imageQuotientGrading W F hF).nested).map n
        ((exactOriginalPrespectrumMap W V hF).map n x) :=
  (imageQuotientPrespectrumNullhomotopy W F hF).at_zero n x

example (n : ℕ) (x : (originalPrespectrum W).space n) :
    (imageQuotientPrespectrumNullhomotopy W F hF).level n (1, x) =
      (originalPrespectrum (imageQuotientGrading W F hF).coarseStructure).point n :=
  (imageQuotientPrespectrumNullhomotopy W F hF).at_one n x

-- The null-track coordinate and the structure-loop coordinate remain independent.
example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum W).space n) :
    (imageQuotientPrespectrumNullhomotopy W F hF).level (n + 1)
        (s, (originalPrespectrum W).structureMap n x t) =
      (originalPrespectrum (imageQuotientGrading W F hF).coarseStructure).structureMap n
        ((imageQuotientPrespectrumNullhomotopy W F hF).level n (s, x)) t :=
  (imageQuotientPrespectrumNullhomotopy W F hF).comm n s x t

example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum W).space n) :
    (mappingCone (exactOriginalPrespectrumMap W V hF)).structureMap n
        (ReducedMappingCone.cylinder ((originalPrespectrum W).point n)
          ((originalPrespectrum V).point n) ((exactOriginalPrespectrumMap W V hF).map n)
          (s, x)) t =
      ReducedMappingCone.cylinder ((originalPrespectrum W).point (n + 1))
        ((originalPrespectrum V).point (n + 1))
        ((exactOriginalPrespectrumMap W V hF).map (n + 1))
        (s, (originalPrespectrum W).structureMap n x t) := rfl

-- The native actual K₀ maps provide kernel/image and surjectivity with exactly this premise.
example (T : FunctorialFactorization V.asSmall) :
    (KMap hF 0).range =
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0).ker :=
  imageQuotient_changeWeakKMap_range_ker W F hF T

example (T : FunctorialFactorization V.asSmall) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0) :=
  imageQuotient_changeWeakKMap_surjective W F hF T

-- No excision, Omega, connectivity, K₀-surjectivity or chosen-zero-image premise is added.
example (T : FunctorialFactorization V.asSmall) :
    Function.Bijective ((stableHomotopyFunctor 0).map (imageQuotientConeMap W F hF)) :=
  imageQuotientConeMap_stable_zero_bijective W F hF T
