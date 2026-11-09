/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionPrespectrum
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Actual affine section coefficient-row consumers

The concrete nonflat map from the integers to ZMod 2 and the subsequent diagonal into its
square exercise two nonidentity coefficient arrows. All models and maps are constructed
from actual native geometry, with no supplied pseudofunctor or equivalence profile.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules
namespace ColibTest.BoundedFlatAffineSectionPrespectrum

universe u

/-- Prove the literal structural formula before specializing the actual coefficient rings. -/
theorem canonicalReindexObject {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    (((boundedAboveFlatAffineSectionsMap f).obj
      (boundedAboveFlatAffinePullbackSection R x)).obj.val.obj (Under.mk g)).fiber =
      (boundedAboveFlatPerfectPullback (Spec.map (f ≫ g))).obj x := rfl

/-- Reduction modulo two is a genuine nonflat coefficient map. -/
def modTwo : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (Int.castRingHom (ZMod 2))

/-- A second nonidentity coefficient arrow, into a different ring. -/
def diagonal : CommRingCat.of (ZMod 2) ⟶ CommRingCat.of (ZMod 2 × ZMod 2) :=
  CommRingCat.ofHom ((RingHom.id (ZMod 2)).prod (RingHom.id (ZMod 2)))

example : ¬ Module.Flat ℤ (ZMod 2) := by
  intro h
  let := h
  have hz : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  rcases smul_eq_zero.mp hz with h₂ | h₁
  · exact (by decide : (2 : ℤ) ≠ 0) h₂
  · exact one_ne_zero h₁

example : ¬ Function.Injective modTwo.hom := by
  intro h
  have he : modTwo.hom 0 = modTwo.hom 2 := by decide
  exact (by decide : (0 : ℤ) ≠ 2) (h he)

example : ¬ Function.Surjective diagonal.hom := by
  intro h
  obtain ⟨x, hx⟩ := h (0, 1)
  have h₀ : x = 0 := congrArg Prod.fst hx
  have h₁ : x = 1 := congrArg Prod.snd hx
  exact zero_ne_one (h₀.symm.trans h₁)

/-- No Flat instance is requested to construct the actual exact coefficient restriction. -/
example : IsExact (boundedAboveFlatAffineSectionWaldhausen (CommRingCat.of ℤ)).cof
    (boundedAboveFlatAffineSectionWaldhausen (CommRingCat.of ℤ)).weq
    (boundedAboveFlatAffineSectionWaldhausen (CommRingCat.of (ZMod 2))).cof
    (boundedAboveFlatAffineSectionWaldhausen (CommRingCat.of (ZMod 2))).weq
    (boundedAboveFlatAffineSectionsMap modTwo) := boundedAboveFlatAffineSectionsMap_exact modTwo

example (x : (boundedAboveFlatPerfectComplex
    (Spec (CommRingCat.of ℤ)).toRingedSpace).FullSubcategory) :
    (((boundedAboveFlatAffineSectionsMap modTwo).obj
      (boundedAboveFlatAffinePullbackSection (CommRingCat.of ℤ) x)).obj.val.obj
        (Under.mk diagonal)).fiber =
      (boundedAboveFlatPerfectPullback (Spec.map (modTwo ≫ diagonal))).obj x :=
  canonicalReindexObject modTwo diagonal x

example : boundedAboveFlatAffineSectionModelMap (modTwo ≫ diagonal) =
    boundedAboveFlatAffineSectionModelMap modTwo ≫
      boundedAboveFlatAffineSectionModelMap diagonal :=
  boundedAboveFlatAffineSectionModelFunctor.map_comp modTwo diagonal

example : boundedAboveFlatAffineSectionPrespectrumFunctor.map (modTwo ≫ diagonal) =
    boundedAboveFlatAffineSectionPrespectrumFunctor.map modTwo ≫
      boundedAboveFlatAffineSectionPrespectrumFunctor.map diagonal :=
  boundedAboveFlatAffineSectionPrespectrumFunctor.map_comp modTwo diagonal

variable (R : CommRingCat.{u})

example : SmallCategory (BoundedAboveFlatAffineSections R) := inferInstance

example : (boundedAboveFlatAffineOriginalEvaluation R).IsEquivalence := inferInstance

example (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory)
    {S : CommRingCat.{u}} (f : R ⟶ S) :
    ((boundedAboveFlatAffinePullbackSection R x).obj.val.obj (Under.mk f)).fiber =
      (boundedAboveFlatPerfectPullback (Spec.map f)).obj x :=
  boundedAboveFlatAffinePullbackSection_obj f x

example (x : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    Nonempty ((boundedAboveFlatAffineOriginalEvaluation R).obj
      (boundedAboveFlatAffinePullbackSection R x) ≅ x) :=
  ⟨boundedAboveFlatAffineOriginalEvaluationPullbackSectionIso R x⟩

example (j : Under R) :
    (boundedAboveFlatAffineEvaluationAt R j).obj (boundedAboveFlatAffineSectionZero R) =
      (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).zero :=
  boundedAboveFlatAffineEvaluationAt_sectionZero R j

example {S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionsMap f).obj (boundedAboveFlatAffineSectionZero R) =
      boundedAboveFlatAffineSectionZero S :=
  boundedAboveFlatAffineSectionsMap_sectionZero f

example : (boundedAboveFlatAffineOriginalEvaluation R).obj
    (boundedAboveFlatAffineSectionZero R) =
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero :=
  boundedAboveFlatAffineOriginalEvaluation_sectionZero R

example {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) :
    (boundedAboveFlatAffineSectionWaldhausen R).cof a ↔
      ∀ j : Under R, (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).cof
        ((boundedAboveFlatAffineEvaluationAt R j).map a) :=
  boundedAboveFlatAffineSectionWaldhausen_cof_iff R a

example {s t : BoundedAboveFlatAffineSections R} (a : s ⟶ t) :
    (boundedAboveFlatAffineSectionWaldhausen R).weq a ↔
      ∀ j : Under R, (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).weq
        ((boundedAboveFlatAffineEvaluationAt R j).map a) :=
  boundedAboveFlatAffineSectionWaldhausen_weq_iff R a

/-- Actual pushout preservation requires, and retains, the cofibration hypothesis. -/
example {S : CommRingCat.{u}} (φ : R ⟶ S)
    {A B D P : BoundedAboveFlatAffineSections R}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    (hi : (boundedAboveFlatAffineSectionWaldhausen R).cof i) (h : IsPushout i f g j) :
    IsPushout ((boundedAboveFlatAffineSectionsMap φ).map i)
      ((boundedAboveFlatAffineSectionsMap φ).map f)
      ((boundedAboveFlatAffineSectionsMap φ).map g)
      ((boundedAboveFlatAffineSectionsMap φ).map j) :=
  (boundedAboveFlatAffineSectionsMap_exact φ).pushout hi h

example : boundedAboveFlatAffineSectionModelMap (𝟙 R) =
    𝟙 (boundedAboveFlatAffineSectionModel R) := boundedAboveFlatAffineSectionModelFunctor.map_id R

example : boundedAboveFlatAffineSectionPrespectrumFunctor.map (𝟙 R) =
    𝟙 (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R) :=
  boundedAboveFlatAffineSectionPrespectrumFunctor.map_id R

example {S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S =
      boundedAboveFlatAffineEvaluationAt R (Under.mk f) :=
  boundedAboveFlatAffineSectionsMap_comp_evaluation f

/-- The concrete nonflat coefficient map retains the original degree-zero K-map. -/
example (a : (boundedAboveFlatAffineSectionWaldhausen (CommRingCat.of ℤ)).K 0) :
    boundedAboveFlatAffineSectionZeroSpaceEquiv (CommRingCat.of (ZMod 2)) 0
        (KMap (boundedAboveFlatAffineSectionsMap_exact modTwo) 0 a) =
      HomotopyGroup.map ((boundedAboveFlatAffineSectionPrespectrumFunctor.map modTwo).map 0)
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map modTwo).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv (CommRingCat.of ℤ) 0 a) :=
  boundedAboveFlatAffineSectionZeroSpaceEquiv_naturality modTwo 0 a

end ColibTest.BoundedFlatAffineSectionPrespectrum
