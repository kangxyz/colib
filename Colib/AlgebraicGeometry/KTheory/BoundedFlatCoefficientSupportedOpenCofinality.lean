/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientEvaluationKComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedEvaluationJoint
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedPerfectEvaluation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenRestrictionKComparison
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenQcqsComparison


/-!
# Cofinality of the actual supported native coefficient restriction

The original supported evaluation equivalence compares the native fine and
relative-open structures with their actual bounded-flat geometric structures.
The original restriction square then transports the installed supported
perfect cofinality theorem to the same r_Z. Both endpoints are compact, the
ambient endpoint is quasi-separated, and the auxiliary support complement is
compact. No density, image, flatness or localization premise is supplied.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- Original supported evaluation computes the actual fine supported fiber K-groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:49"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
def boundedAboveFlatCoefficientSupportedSectionKEquiv {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).K n ≃*
      (boundedAboveFlatPerfectSupportedWaldhausen j).K n :=
  boundedAboveFlatCoefficientEvaluationKEquiv
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen j)
    (boundedAboveFlatPerfectSupportedWaldhausen j)
      (boundedAboveFlatCoefficientSupportedSectionEquivalence j)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact j)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact j) n

/-- This comparison keeps the original supported evaluated object's honest K-zero class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:59"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedSectionKEquiv_objectClass
    {i : Index R} {U : Scheme.{u}} (j : U ⟶ space i) [IsOpenImmersion j]
    (S : BoundedAboveFlatCoefficientSupportedSections j) :
    boundedAboveFlatCoefficientSupportedSectionKEquiv j 0
        ((boundedAboveFlatCoefficientSupportedSectionWaldhausen j).kZeroObjectClass S) =
      (boundedAboveFlatPerfectSupportedWaldhausen j).kZeroObjectClass
        ((boundedAboveFlatCoefficientSupportedEvaluation j).obj S) := by
  let W := boundedAboveFlatPerfectSupportedWaldhausen j
  apply (W.asSmallKEquiv 0).injective
  change W.asSmallKEquiv 0 ((W.asSmallKEquiv 0).symm
    (KMap ((boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact j).comp
      W.asSmall_up_exact) 0
      ((boundedAboveFlatCoefficientSupportedSectionWaldhausen j).kZeroObjectClass S))) = _
  rw [MulEquiv.apply_symm_apply, Structure.asSmallKEquiv_objectClass]
  rw [← boundedAboveFlatCoefficientSupportedSectionEquivalence_functor j]
  exact KMap_kZeroObjectClass
    ((boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact j).comp
      W.asSmall_up_exact) S

private theorem inverse_weq_of_equivalence {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (V : Structure C) (W : Structure D)
    (h : ∀ {A B : C} (p : A ⟶ B), V.weq p ↔ W.weq (e.functor.map p))
    {A B : D} (p : A ⟶ B) (hp : W.weq p) : V.weq (e.inverse.map p) := by
  apply (h _).mpr
  have hm : e.functor.map (e.inverse.map p) =
      e.counitIso.hom.app _ ≫ p ≫ e.counitIso.inv.app _ := by
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id] using
      congrArg (fun k ↦ k ≫ e.counitIso.inv.app _) (e.counitIso.hom.naturality p)
  rw [hm]
  exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _ hp (W.weq_iso _ inferInstance))

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The inverse of original supported evaluation is exact for the same relative-open structures.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:115"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenEquivalence_inverse_exact (a : Under R) :
    IsExact
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).weq
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedAboveFlatCoefficientSupportedSectionEquivalence
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).inverse where
  zero := (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).zero
  cofibration := (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).cofibration
  weak p hp := inverse_weq_of_equivalence
    (boundedAboveFlatCoefficientSupportedSectionEquivalence
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
    (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a))
    (fun q ↦ by
      rw [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a q) p hp
  pushout := (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).pushout

/-- The literal forward supported equivalence is exact for the actual coarse structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:141"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenEquivalence_functor_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).weq
      (boundedAboveFlatCoefficientSupportedSectionEquivalence
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).functor := by
  rw [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
  exact boundedAboveFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a

/-- Original supported evaluation computes the actual bounded-flat relative-open K-groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:154"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
def boundedAboveFlatCoefficientSupportedOpenKEquiv (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K n ≃*
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).K n :=
  boundedAboveFlatCoefficientEvaluationKEquiv (boundedAboveFlatCoefficientSupportedOpenWaldhausen
    f T a)
    (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
    (boundedAboveFlatCoefficientSupportedOpenEquivalence_functor_exact f T a)
    (boundedAboveFlatCoefficientSupportedOpenEquivalence_inverse_exact f T a) n

/-- The genuine supported evaluation square retains the original geometric restriction K-map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:166"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_KComparison (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K n) :
    boundedAboveFlatCoefficientSupportedSectionKEquiv (boundedAboveFlatCoefficientOpenSupportOpen
      f T a).ι n
        (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n x) =
      boundedAboveFlatPerfectSupportedOpenKRestrict (schemeMap f a) n
        (boundedAboveFlatCoefficientSupportedOpenKEquiv f T a n x) :=
  boundedAboveFlatCoefficientEvaluationKEquiv_natural
    (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
    (boundedAboveFlatCoefficientSupportedOpenEquivalence_functor_exact f T a)
    (boundedAboveFlatCoefficientSupportedOpenEquivalence_inverse_exact f T a)
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedAboveFlatPerfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T
      a).ι)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a)
    (boundedAboveFlatPerfectSupportedOpenRestriction_isExact
      (T := boundedAboveFlatCoefficientSupportOpen Q T a) (schemeMap f a))
    (by
      simp only [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedAboveFlatCoefficientSupportedOpenRestrictionEvaluationIso f T a) n x

/-- The native supported open evaluation followed by the genuine supported perfect comparison.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:198"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
def boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv [CompactSpace P.left]
    (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).K n ≃*
      (perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).K n := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  exact (boundedAboveFlatCoefficientSupportedSectionKEquiv
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι n).trans
    (boundedAboveFlatPerfectSupportedKEquiv (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι n)

omit [IsOpenImmersion f.left] in
/-- The supported perfect comparison retains the original supported evaluated K-zero class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:210"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv_objectClass [CompactSpace P.left]
    (a : Under R) (S : BoundedAboveFlatCoefficientSupportedOpenSections f T a) :
    boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0
        ((boundedAboveFlatCoefficientSupportedSectionWaldhausen
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S) =
      (perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).kZeroObjectClass
        ((boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a).obj S) := by
  change boundedAboveFlatPerfectSupportedToPerfectKMap
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι 0
      (boundedAboveFlatCoefficientSupportedSectionKEquiv
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι 0
        ((boundedAboveFlatCoefficientSupportedSectionWaldhausen
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S)) = _
  rw [boundedAboveFlatCoefficientSupportedSectionKEquiv_objectClass]
  exact KMap_kZeroObjectClass
    (boundedAboveFlatPerfectSupportedInclusion_isExact (boundedAboveFlatCoefficientOpenSupportOpen
      f T a).ι) _

/-- Original supported coarse evaluation followed by the genuine relative supported comparison.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:229"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
def boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv [CompactSpace Q.left]
    (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K n ≃*
      (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).K n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedAboveFlatCoefficientSupportedOpenKEquiv f T a n).trans
    (boundedAboveFlatPerfectSupportedOpenKEquiv (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a) n)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The unchanged native r_Z compares with the original supported perfect restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:242"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_perfectKComparison
    (a : Under R) (n : ℕ) (x : (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K n) :
    boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a n
        (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n x) =
      perfectSupportedOpenKRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a) n
        (boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv f T a n x) := by
  change boundedAboveFlatPerfectSupportedToPerfectKMap
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι n
      (boundedAboveFlatCoefficientSupportedSectionKEquiv
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι n
        (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n x)) =
    perfectSupportedOpenKRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a) n
      (boundedAboveFlatPerfectSupportedOpenToPerfectKMap (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a) n
        (boundedAboveFlatCoefficientSupportedOpenKEquiv f T a n x))
  rw [boundedAboveFlatCoefficientSupportedOpenRestriction_KComparison]
  exact (DFunLike.congr_fun (boundedAboveFlatPerfectSupportedOpenKRestrict_comparison
    (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a) n)
    (boundedAboveFlatCoefficientSupportedOpenKEquiv f T a n x)).symm

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Installed supported qcqs cofinality proves the original native r_Z injective in every degree.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:266"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_injective (a : Under R) (n : ℕ) :
    Function.Injective (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n)
      := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  let : CompactSpace (boundedAboveFlatCoefficientSupportOpen Q T a) :=
    boundedAboveFlatCoefficientSupportOpen_compactSpace Q T a
  have hT : IsCompact (boundedAboveFlatCoefficientSupportOpen Q T a : Set (space (op Q, a))) :=
    isCompact_iff_compactSpace.mpr
      (show CompactSpace (boundedAboveFlatCoefficientSupportOpen Q T a) from inferInstance)
  intro x y hxy
  apply (boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv f T a n).injective
  apply perfectSupportedOpenKRestrict_injective_of_qcqs (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a)
    hT n
  rw [← boundedAboveFlatCoefficientSupportedOpenRestriction_perfectKComparison f T a n x,
    ← boundedAboveFlatCoefficientSupportedOpenRestriction_perfectKComparison f T a n y, hxy]

/-- Actual supported r_Z is injective on the honest degree-zero endpoint. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:285"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_zero_injective (a : Under R) :
    Function.Injective (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) 0) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_injective f T a 0

/-- Installed supported cofinality proves the same original r_Z bijective in positive degrees. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:290"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_succ_bijective
    (a : Under R) (n : ℕ) :
    Function.Bijective (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) (n
      + 1))
    := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  let : CompactSpace (boundedAboveFlatCoefficientSupportOpen Q T a) :=
    boundedAboveFlatCoefficientSupportOpen_compactSpace Q T a
  have hT : IsCompact (boundedAboveFlatCoefficientSupportOpen Q T a : Set (space (op Q, a))) :=
    isCompact_iff_compactSpace.mpr
      (show CompactSpace (boundedAboveFlatCoefficientSupportOpen Q T a) from inferInstance)
  refine ⟨boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_injective f T a (n + 1), ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (perfectSupportedOpenKRestrict_succ_bijective_of_qcqs (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a) hT
    n).surjective (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a (n + 1) y)
  refine ⟨(boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1)).symm z, ?_⟩
  apply (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a (n + 1)).injective
  rw [boundedAboveFlatCoefficientSupportedOpenRestriction_perfectKComparison,
    MulEquiv.apply_symm_apply]
  exact hz

end AlgebraicGeometry.Scheme.Modules
