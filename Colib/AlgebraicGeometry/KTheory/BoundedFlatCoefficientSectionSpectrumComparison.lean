/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySectionKComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionPrespectrum
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectComparison
public import Colib.KTheory.Waldhausen.Iterated.ModelStableKMap
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality

/-!
# Pointwise spectrum evaluation of the original native coefficient sections

Every joint fiber uses its original fine section Model and the one joint zero.
Original identity evaluation is lifted by the common-universe `AsSmall` equivalence,
then canonically rebased to the chosen lifted bounded-flat zero. The resulting actual
prespectrum arrow retains the original forward K-equations, including degree zero.
The bounded-flat map is stable in every signed degree without compactness; the original
perfect inclusion is stable when the specified scheme over the base is quasi-compact.
Naturality and actual geometric comparison tracks are supplied separately.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}

/-- Original identity evaluation lifted through the existing common-universe equivalence. -/
def boundedAboveFlatCoefficientSectionSmallEquivalence (i : Index R) :
    BoundedAboveFlatCoefficientSections i ≌ AsSmall.{0} (boundedAboveFlatPerfectComplex (space
      i).toRingedSpace).FullSubcategory :=
  (boundedAboveFlatCoefficientSectionEquivalence i).trans AsSmall.equiv

/-- The actual lifted evaluation preserves the original transported section classes. -/
theorem boundedAboveFlatCoefficientSectionSmallEquivalence_exact (i : Index R) :
    IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.weq
      (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor :=
  (boundedAboveFlatCoefficientOriginalEvaluation_exact i).comp
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall_up_exact

/-- The inverse lowers only the universe before applying the actual evaluation inverse. -/
theorem boundedAboveFlatCoefficientSectionSmallEquivalence_inverse_exact (i : Index R) :
    IsExact (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.weq
      (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatCoefficientSectionSmallEquivalence i).inverse :=
  (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall_down_exact.comp
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact i)

/-- The forward map is the original lifted evaluation K-map, then universe lowering. -/
theorem boundedAboveFlatCoefficientSectionKEquiv_apply (i : Index R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSectionWaldhausen i).K n) :
    boundedAboveFlatCoefficientSectionKEquiv i n x =
      ((boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmallKEquiv n).symm
        (KMap (boundedAboveFlatCoefficientSectionSmallEquivalence_exact i) n x) := rfl

/-- Evaluation followed by the unchanged original bounded-flat inclusion on a compact fiber. -/
def boundedAboveFlatCoefficientSectionPerfectKEquiv (i : Index R)
    [CompactSpace i.1.unop.left] (n : ℕ) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).K n ≃*
      (perfectComplexesWaldhausen (space i).toRingedSpace).K n := by
  letI : CompactSpace (space i) := compactSpace_space i
  exact (boundedAboveFlatCoefficientSectionKEquiv i n).trans (boundedAboveFlatPerfectKEquiv
      (space i).toRingedSpace n)

/-- The perfect forward map is precisely the original inclusion after identity evaluation. -/
theorem boundedAboveFlatCoefficientSectionPerfectKEquiv_apply (i : Index R)
    [CompactSpace i.1.unop.left] (n : ℕ)
    (x : (boundedAboveFlatCoefficientSectionWaldhausen i).K n) :
    boundedAboveFlatCoefficientSectionPerfectKEquiv i n x =
      boundedAboveFlatPerfectToPerfectKMap (space i).toRingedSpace n
        (boundedAboveFlatCoefficientSectionKEquiv i n x) := rfl

/-- The actual lifted evaluation image zero has its unique iso to the target's chosen zero. -/
def boundedAboveFlatCoefficientSectionEvaluationZeroIso (i : Index R) :
    (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor.obj
        (boundedAboveFlatCoefficientSectionWaldhausen i).zero ≅
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.zero :=
  ((boundedAboveFlatCoefficientSectionSmallEquivalence_exact i).zero
    (boundedAboveFlatCoefficientSectionWaldhausen i).isZero).iso
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.isZero

/-- Normalize that original lifted evaluation on the actual direct section Model. -/
def boundedAboveFlatCoefficientSectionEvaluationModelMap (i : Index R) :
    boundedAboveFlatCoefficientSectionModel i ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace) :=
  ⟨⟨CategoryTheory.rebaseFunctor
    (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor
    (boundedAboveFlatCoefficientSectionWaldhausen i).zero
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.zero
    (boundedAboveFlatCoefficientSectionEvaluationZeroIso i),
    (boundedAboveFlatCoefficientSectionSmallEquivalence_exact i).rebase⟩,
    CategoryTheory.rebaseFunctor_obj_base _ _ _ _⟩

/-- The whole actual normalization retains a natural iso from the original lifted evaluation. -/
def boundedAboveFlatCoefficientSectionEvaluationNormalizationIso (i : Index R) :
    (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor ≅
      (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.toFunctor :=
  CategoryTheory.rebaseFunctorIso
    (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor
    (boundedAboveFlatCoefficientSectionWaldhausen i).zero
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.zero
    (boundedAboveFlatCoefficientSectionEvaluationZeroIso i)

/-- The normalization sends the original section zero to the specified lifted zero literally. -/
theorem boundedAboveFlatCoefficientSectionEvaluationModelMap_zero (i : Index R) :
    (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.toFunctor.obj
        (boundedAboveFlatCoefficientSectionWaldhausen i).zero =
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmall.zero :=
  (boundedAboveFlatCoefficientSectionEvaluationModelMap i).property

/-- The genuine map keeps the direct source and the target's explicit common-universe lift. -/
def boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap (i : Index R) :
    (boundedAboveFlatCoefficientSectionPrespectrumFunctor R).obj i ⟶
      originalPrespectrum (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace) :=
  prespectrumMap (boundedAboveFlatCoefficientSectionEvaluationModelMap i)

/-- Normalization leaves precisely the original lifted evaluation K-map after universe lifting. -/
theorem boundedAboveFlatCoefficientSectionEvaluationModelMap_KMap
    (i : Index R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSectionWaldhausen i).K n) :
    KMap (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.isExact n x =
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmallKEquiv n
        (boundedAboveFlatCoefficientSectionKEquiv i n x) := by
  change KMap (boundedAboveFlatCoefficientSectionSmallEquivalence_exact i).rebase n x = _
  rw [boundedAboveFlatCoefficientSectionKEquiv_apply, MulEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun
    (KMap_eq_of_iso (boundedAboveFlatCoefficientSectionSmallEquivalence_exact i)
      (boundedAboveFlatCoefficientSectionSmallEquivalence_exact i).rebase
      (boundedAboveFlatCoefficientSectionEvaluationNormalizationIso i) n) x).symm

/-- The original section K-equivalence is the actual nonnegative stable map of evaluation. -/
theorem boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_KEquiv
    (i : Index R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSectionWaldhausen i).K n) :
    originalKStableEquiv (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace) n
        (Additive.ofMul (boundedAboveFlatCoefficientSectionKEquiv i n x)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSectionModel i) n
          (Additive.ofMul x)) := by
  change smallModelKStableEquiv
      (asSmallCategory (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace)) n
      (Additive.ofMul ((boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmallKEquiv n
        (boundedAboveFlatCoefficientSectionKEquiv i n x))) = _
  rw [← boundedAboveFlatCoefficientSectionEvaluationModelMap_KMap]
  exact smallModelKStableEquiv_naturality
    (boundedAboveFlatCoefficientSectionEvaluationModelMap i) n x

/-- This actual evaluation arrow is stable in every signed degree without compactness. -/
theorem boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence
    (i : Index R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i) := by
  change IsStableEquivalence
    (prespectrumMap (boundedAboveFlatCoefficientSectionEvaluationModelMap i))
  have hK (n : ℕ) : Function.Bijective
      (KMap (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.isExact n) := by
    have he :
        (fun x ↦ KMap (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.isExact n x) =
        (fun x ↦ (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmallKEquiv n
          (boundedAboveFlatCoefficientSectionKEquiv i n x)) := by
      funext x
      exact boundedAboveFlatCoefficientSectionEvaluationModelMap_KMap i n x
    change Function.Bijective (fun x ↦
      KMap (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.isExact n x)
    rw [he]
    exact ((boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).asSmallKEquiv
      n).bijective.comp
      (boundedAboveFlatCoefficientSectionKEquiv i n).bijective
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hd : d < 0
  · let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (boundedAboveFlatCoefficientSectionModel i))) :=
      prespectrum_stableHomotopyGroup_neg_subsingleton
        (boundedAboveFlatCoefficientSectionModel i) d hd
    let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (asSmallCategory (boundedAboveFlatPerfectWaldhausen (space
      i).toRingedSpace)))) :=
      prespectrum_stableHomotopyGroup_neg_subsingleton
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace)) d hd
    exact Function.bijective_of_subsingleton' _
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact ⟨prespectrumMap_stable_nonnegative_injective
      (boundedAboveFlatCoefficientSectionEvaluationModelMap i) d.toNat (hK d.toNat).1,
      prespectrumMap_stable_nonnegative_surjective
        (boundedAboveFlatCoefficientSectionEvaluationModelMap i) d.toNat (hK d.toNat).2⟩

/-- Compose with the original normalized bounded-flat inclusion into the lifted perfect spectrum. -/
def boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (i : Index R) :
    (boundedAboveFlatCoefficientSectionPrespectrumFunctor R).obj i ⟶
      originalPrespectrum (perfectComplexesWaldhausen (space i).toRingedSpace) :=
  boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i ≫
    exactOriginalPrespectrumMap (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace)
      (perfectComplexesWaldhausen (space i).toRingedSpace)
      (boundedAboveFlatPerfectInclusion_isExact (space i).toRingedSpace)

/-- The perfect stable map retains the literal original inclusion K-map after evaluation. -/
theorem boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KMap
    (i : Index R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSectionWaldhausen i).K n) :
    originalKStableEquiv (perfectComplexesWaldhausen (space i).toRingedSpace) n
        (Additive.ofMul (boundedAboveFlatPerfectToPerfectKMap (space i).toRingedSpace n
          (boundedAboveFlatCoefficientSectionKEquiv i n x))) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap i)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSectionModel i) n
          (Additive.ofMul x)) := by
  have h := originalKStableEquiv_exact_naturality
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace) (perfectComplexesWaldhausen
      (space i).toRingedSpace)
    (boundedAboveFlatPerfectInclusion_isExact (space i).toRingedSpace) n
    (boundedAboveFlatCoefficientSectionKEquiv i n x)
  rw [boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_KEquiv] at h
  exact h.trans (by rw [boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap,
    Functor.map_comp]; rfl)


/-- Compactness is used only to make the original perfect inclusion a stable equivalence. -/
theorem boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence
    (i : Index R) [CompactSpace i.1.unop.left] :
    IsStableEquivalence
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap i) := by
  let : CompactSpace (space i) := compactSpace_space i
  apply IsStableEquivalence.comp
    (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence i)
  apply (exactOriginalPrespectrumMap_isStableEquivalence_iff
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace) (perfectComplexesWaldhausen
      (space i).toRingedSpace)
    (boundedAboveFlatPerfectInclusion_isExact (space i).toRingedSpace)).mpr
  exact boundedAboveFlatPerfectToPerfectKMap_bijective (space i).toRingedSpace

/-- Under compactness the same actual perfect map is the existing section perfect K-equivalence. -/
theorem boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv
    (i : Index R) [CompactSpace i.1.unop.left] (n : ℕ)
    (x : (boundedAboveFlatCoefficientSectionWaldhausen i).K n) :
    originalKStableEquiv (perfectComplexesWaldhausen (space i).toRingedSpace) n
        (Additive.ofMul (boundedAboveFlatCoefficientSectionPerfectKEquiv i n x)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap i)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSectionModel i) n
          (Additive.ofMul x)) := by
  rw [boundedAboveFlatCoefficientSectionPerfectKEquiv_apply]
  exact boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KMap i n x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:37"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionSmallEquivalence

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:42"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionSmallEquivalence_exact

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:52"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionSmallEquivalence_inverse_exact

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:62"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionKEquiv_apply

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:69"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectKEquiv

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:77"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectKEquiv_apply

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:85"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationZeroIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:94"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationModelMap

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:106"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationNormalizationIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:116"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationModelMap_zero

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:123"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:129"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationModelMap_KMap

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:143"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_KEquiv

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:163"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:201"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:209"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KMap

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:230"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionSpectrumComparison.lean:243"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv


end AlgebraicGeometry.Scheme.Modules
