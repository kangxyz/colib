/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.PrimarySmallModel
public import Colib.KTheory.Quillen.FiniteSupport.Decomposition
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization

/-!
# Original-map primary assembly for native Dedekind torsion support

The source is the actual native `smallTorsion R⁰` category of finite-module localization.
One exact functor has that small source and the small finite-support primary-family target;
large intermediate categories are used only inside that exact functor. Its original normalized
K-map is the forward map of the K-equivalence. The primary direct-sum assembly retains the
original `nativePrimaryInclusionExactFunctor.KMap` maps.

`primaryAssemblyKEquiv R n` identifies the direct sum of point-primary K-groups in index
`n + 1` with the actual `SupportedG R⁰ (n + 1)`. Its singleton and finite-sum formulas use the
original primary inclusions. `supportedKMap_comp_primaryAssembly` retains the original ambient
G-theory map, including its standard-to-transported small exact-structure comparison. The
index-one and index-two specializations are explicit.

Point-primary categories consist of finite modules killed by prime-ideal powers. This is
primary assembly; residue-field dévissage and the residue-field versus quotient-ring comparison
are separate obligations. All K-groups below use the same native universe.

## Implementation provenance

Adapted from `Quillen/GTheory/Dedekind/PrimarySupport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native finite modules, actual
localization kernel, canonical scalar restrictions and original normalized K-maps are retained.
The standard exact structures use Colib's native abelian structures directly.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Abelian CategoryTheory.Abelian.Devissage
open FGModuleCat.PrimaryDecomposition
open scoped nonZeroDivisors DirectSum ZeroObject

namespace FGModuleCat.DedekindPrimary

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The actual chosen lower-universe category of point-primary modules. -/
abbrev PrimaryCategory (p : IsDedekindDomain.HeightOneSpectrum R) : Type u :=
  SmallModel.{u} (PrimaryModule R p.asIdeal)

/-- The standard abelian exact structure on the actual point-primary category. -/
abbrev primaryExactStructure (p : IsDedekindDomain.HeightOneSpectrum R) :=
  abelianExactStructure (PrimaryCategory R p)

/-- Original K-groups of actual point-primary modules in the native small model. -/
abbrev PrimaryK (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :=
  (primaryExactStructure R p).K n

instance nativePrimaryFunctor_isEquivalence :
    (nativePrimaryExactFunctor R).toFunctor.IsEquivalence :=
  (nativePrimaryEquivalence R).isEquivalence_functor

/-- Reflection of actual monomorphisms and epimorphisms makes the original Q-map an equivalence. -/
instance nativePrimary_mapQ_isEquivalence : (nativePrimaryExactFunctor R).mapQ.IsEquivalence := by
  apply (nativePrimaryExactFunctor R).mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    exact (abelianExactStructure_inflation_iff (NativeSmallTorsion R) i).2
      ((nativePrimaryExactFunctor R).toFunctor.mono_of_mono_map
        ((Pi.finiteCategoryExactStructure (PrimaryCategory R)).mono_of_inflation hi))
  · intro X Y p hp
    exact (abelianExactStructure_deflation_iff (NativeSmallTorsion R) p).2
      ((nativePrimaryExactFunctor R).toFunctor.epi_of_epi_map
        ((Pi.finiteCategoryExactStructure (PrimaryCategory R)).epi_of_deflation hp))

/-- The actual original support-to-primary-family K-map, bundled as its genuine equivalence. -/
def primaryKEquiv (n : ℕ) : FGModuleCat.Localization.SupportedG (nonZeroDivisors R) n ≃*
    (Pi.finiteCategoryExactStructure (PrimaryCategory R)).K n :=
  (nativePrimaryExactFunctor R).KEquivOfMapQIsEquivalence n

@[simp]
theorem primaryKEquiv_toMonoidHom (n : ℕ) :
    ((primaryKEquiv R n).toMonoidHom : FGModuleCat.Localization.SupportedG (nonZeroDivisors R) n →*
      (Pi.finiteCategoryExactStructure (PrimaryCategory R)).K n) =
      (nativePrimaryExactFunctor R).KMap n := rfl

/-- The original primary evaluation, as one exact functor at the small endpoints. -/
def primaryEvaluationExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactFunctor
      (abelianExactStructure (FGModuleCat.Localization.supported (nonZeroDivisors
        R)).FullSubcategory)
      (primaryExactStructure R p) :=
  (nativePrimaryExactFunctor R).comp (Pi.finiteCategoryEvaluation (PrimaryCategory R) p)

/-- Cancel only the canonical support counit inside the actual endpoint composite. -/
def inclusionEvaluationComparisonIso (p q : IsDedekindDomain.HeightOneSpectrum R) :
    ((nativePrimaryInclusionExactFunctor R p).comp
      (primaryEvaluationExactFunctor R q)).toFunctor ≅
      (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙ primaryToTorsion R p ⋙
        torsionPrimaryFunctor R q.asIdeal ⋙
        (equivSmallModel.{u} (PrimaryModule R q.asIdeal)).functor := by
  let F := (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙ primaryToTorsion R p
  let G := torsionPrimaryFunctor R q.asIdeal ⋙
    (equivSmallModel.{u} (PrimaryModule R q.asIdeal)).functor
  change F ⋙ (smallTorsionEquivalence R).inverse ⋙ (smallTorsionEquivalence R).functor ⋙ G ≅ F ⋙ G
  exact Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight (smallTorsionEquivalence R).counitIso G) ≪≫
    Functor.isoWhiskerLeft F (Functor.leftUnitor G)

/-- The original primary inclusion followed by its own coordinate is canonically the identity. -/
def inclusionSelfEvaluationIso (p : IsDedekindDomain.HeightOneSpectrum R) :
    ((nativePrimaryInclusionExactFunctor R p).comp
      (primaryEvaluationExactFunctor R p)).toFunctor ≅
      (ExactFunctor.id (primaryExactStructure R p)).toFunctor := by
  let e := equivSmallModel.{u} (PrimaryModule R p.asIdeal)
  exact inclusionEvaluationComparisonIso R p p ≪≫
    Functor.isoWhiskerLeft e.inverse
      (Functor.isoWhiskerRight (primaryInclusionComponentIso R p) e.functor) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.leftUnitor e.functor) ≪≫ e.counitIso

/-- The original primary inclusion has a zero object at every other evaluated coordinate. -/
theorem inclusionOtherEvaluation_isZero (p q : IsDedekindDomain.HeightOneSpectrum R)
    (hpq : p ≠ q) (X : PrimaryCategory R p) :
    IsZero (((nativePrimaryInclusionExactFunctor R p).comp
      (primaryEvaluationExactFunctor R q)).toFunctor.obj X) := by
  have h := (equivSmallModel.{u} (PrimaryModule R q.asIdeal)).functor.map_isZero
    (primaryInclusionOtherComponent_isZero R p q hpq
      ((equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse.obj X))
  exact h.of_iso ((inclusionEvaluationComparisonIso R p q).app X)

/-- Every other evaluated original primary inclusion is the actual zero exact functor. -/
def inclusionOtherEvaluationIso (p q : IsDedekindDomain.HeightOneSpectrum R) (hpq : p ≠ q) :
    ((nativePrimaryInclusionExactFunctor R p).comp
      (primaryEvaluationExactFunctor R q)).toFunctor ≅
      (ExactFunctor.zero (primaryExactStructure R p) (primaryExactStructure R q)).toFunctor :=
  NatIso.ofComponents
    (fun X => (inclusionOtherEvaluation_isZero R p q hpq X).iso (isZero_zero _)) (by
      intro X Y f
      exact (inclusionOtherEvaluation_isZero R p q hpq X).eq_of_src _ _)

/-- The original normalized primary inclusion and its own evaluation induce the identity map. -/
theorem primaryEvaluationKMap_comp_inclusion (n : ℕ)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    ((primaryEvaluationExactFunctor R p).KMap n).comp
        ((nativePrimaryInclusionExactFunctor R p).KMap n) = MonoidHom.id _ := by
  have h := ExactFunctor.KMap_eq_of_natIso (inclusionSelfEvaluationIso R p) n
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_id] at h
  exact h

/-- Every other original normalized primary evaluation is trivial on an included primary factor. -/
theorem primaryEvaluationKMap_comp_inclusion_of_ne (n : ℕ)
    (p q : IsDedekindDomain.HeightOneSpectrum R) (hpq : p ≠ q) :
    ((primaryEvaluationExactFunctor R q).KMap n).comp
        ((nativePrimaryInclusionExactFunctor R p).KMap n) = 1 := by
  have h := ExactFunctor.KMap_eq_of_natIso (inclusionOtherEvaluationIso R p q hpq) n
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_zero] at h
  exact h

/-- The original support K-equivalence sends original primary inclusions to Q2 singleton maps. -/
theorem primaryKEquiv_inclusion (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R)
    (a : PrimaryK R p n) :
    primaryKEquiv R n ((nativePrimaryInclusionExactFunctor R p).KMap n a) =
      (Pi.singletonExactInclusion (PrimaryCategory R) p).KMap n a := by
  apply CategoryTheory.Pi.FiniteSupport.evaluationK_ext (PrimaryCategory R) n
  intro q
  change (Pi.finiteCategoryEvaluation (PrimaryCategory R) q).KMap n
      ((nativePrimaryExactFunctor R).KMap n
        ((nativePrimaryInclusionExactFunctor R p).KMap n a)) = _
  refine (DFunLike.congr_fun
    (ExactFunctor.KMap_comp (nativePrimaryExactFunctor R)
      (Pi.finiteCategoryEvaluation (PrimaryCategory R) q) n)
    ((nativePrimaryInclusionExactFunctor R p).KMap n a)).symm.trans ?_
  by_cases hq : q = p
  · subst q
    exact (DFunLike.congr_fun (primaryEvaluationKMap_comp_inclusion R n p) a).trans
      (CategoryTheory.Pi.FiniteSupport.singletonKMap_evaluation (PrimaryCategory R) n p a).symm
  · exact (DFunLike.congr_fun
      (primaryEvaluationKMap_comp_inclusion_of_ne R n p q (Ne.symm hq)) a).trans
      (CategoryTheory.Pi.FiniteSupport.singletonKMap_evaluation_of_ne
        (PrimaryCategory R) n p q hq a).symm

/-- The primary decomposition consists of the original native primary-evaluation K-maps. -/
def primaryDecompositionKEquiv (n : ℕ) :
    Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) (n + 1)) ≃+
      ⨁ p, Additive (PrimaryK R p (n + 1)) :=
  (primaryKEquiv R (n + 1)).toAdditive.trans
    (CategoryTheory.Pi.FiniteSupport.decompositionKEquiv (PrimaryCategory R) n)

/-- The forward coordinate retains the actual normalized native primary evaluation. -/
@[simp]
theorem primaryDecompositionKEquiv_apply (n : ℕ)
    (a : Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) (n + 1)))
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    primaryDecompositionKEquiv R n a p =
      Additive.ofMul ((primaryEvaluationExactFunctor R p).KMap (n + 1) a.toMul) := by
  change Additive.ofMul ((Pi.finiteCategoryEvaluation (PrimaryCategory R) p).KMap (n + 1)
    ((nativePrimaryExactFunctor R).KMap (n + 1) a.toMul)) = _
  exact congrArg Additive.ofMul (DFunLike.congr_fun
    (ExactFunctor.KMap_comp (nativePrimaryExactFunctor R)
      (Pi.finiteCategoryEvaluation (PrimaryCategory R) p) (n + 1)) a.toMul).symm

/-- Original primary inclusions give the canonical direct-sum insertions. -/
@[simp]
theorem primaryDecompositionKEquiv_inclusion (n : ℕ)
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : PrimaryK R p (n + 1)) :
    primaryDecompositionKEquiv R n
        (Additive.ofMul ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1) a)) =
      DirectSum.of (fun q => Additive (PrimaryK R q (n + 1))) p (Additive.ofMul a) := by
  change CategoryTheory.Pi.FiniteSupport.decompositionKEquiv (PrimaryCategory R) n
    (Additive.ofMul (primaryKEquiv R (n + 1)
      ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1) a))) = _
  rw [primaryKEquiv_inclusion]
  exact CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_singleton (PrimaryCategory R) n p a

/-- Positive-degree primary assembly into the actual native torsion-support group. -/
def primaryAssemblyKEquiv (n : ℕ) :
    (⨁ p, Additive (PrimaryK R p (n + 1))) ≃+
      Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) (n + 1)) :=
  (primaryDecompositionKEquiv R n).symm

/-- Assembly on a singleton is the original native primary-inclusion K-map. -/
@[simp]
theorem primaryAssemblyKEquiv_of (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R)
    (a : Additive (PrimaryK R p (n + 1))) :
    primaryAssemblyKEquiv R n (DirectSum.of _ p a) =
      Additive.ofMul ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1) a.toMul) := by
  apply (primaryDecompositionKEquiv R n).injective
  change primaryDecompositionKEquiv R n
      ((primaryDecompositionKEquiv R n).symm (DirectSum.of _ p a)) = _
  rw [AddEquiv.apply_symm_apply]
  simpa only [ofMul_toMul] using
    (primaryDecompositionKEquiv_inclusion R n p a.toMul).symm

/-- The sum of the original native primary-inclusion K-maps. -/
def primaryAssemblyKMap (n : ℕ) :
    (⨁ p, Additive (PrimaryK R p (n + 1))) →+
      Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) (n + 1)) :=
  DirectSum.toAddMonoid
    (fun p => ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1)).toAdditive)

/-- The genuine assembly equivalence has exactly the sum of original inclusion maps forward. -/
@[simp]
theorem primaryAssemblyKEquiv_toAddMonoidHom (n : ℕ) :
    ((primaryAssemblyKEquiv R n).toAddMonoidHom : (⨁ p, Additive (PrimaryK R p (n + 1))) →+
      Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) (n + 1))) =
      primaryAssemblyKMap R n := by
  apply DirectSum.addHom_ext
  intro p a
  change primaryAssemblyKEquiv R n (DirectSum.of _ p a) =
    primaryAssemblyKMap R n (DirectSum.of _ p a)
  rw [primaryAssemblyKEquiv_of, primaryAssemblyKMap, DirectSum.toAddMonoid_of]
  rfl

/-- Assembly is the actual finite sum over the support of the given direct-sum element. -/
theorem primaryAssemblyKEquiv_eq_sum (n : ℕ)
    (a : ⨁ p, Additive (PrimaryK R p (n + 1))) :
    primaryAssemblyKEquiv R n a = ∑ p ∈ a.support,
      Additive.ofMul ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1) (a p).toMul) := by
  calc
    primaryAssemblyKEquiv R n a = primaryAssemblyKMap R n a :=
      DFunLike.congr_fun (primaryAssemblyKEquiv_toAddMonoidHom R n) a
    _ = primaryAssemblyKMap R n
        (∑ p ∈ a.support, DirectSum.of (fun q => Additive (PrimaryK R q (n + 1))) p (a p)) :=
      congrArg (primaryAssemblyKMap R n) (DirectSum.sum_support_of a).symm
    _ = _ := by
      change (DirectSum.toAddMonoid
        (fun p => ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1)).toAdditive))
        (∑ p ∈ a.support, DirectSum.of (fun q => Additive (PrimaryK R q (n + 1))) p (a p)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact DirectSum.toAddMonoid_of
        (fun p => ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1)).toAdditive) p (a p)

/-- The original represented-primary inclusion, as one exact functor at small endpoints. -/
def primaryAmbientExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactFunctor (primaryExactStructure R p)
      (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R))) :=
  ((nativePrimaryRealizationExactFunctor R p).comp
    (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
    (finiteModuleToNativeSmallExactFunctor R)

/-- The original primary ambient map, with the actual standard-to-transported G comparison. -/
def primaryAmbientKMap (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    PrimaryK R p n →* FGModuleCat.FractionLocalization.G R n :=
  (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).symm.toMonoidHom.comp
    ((primaryAmbientExactFunctor R p).KMap n)

/-- The actual supported map commutes with each original primary inclusion. -/
theorem supportedKMap_comp_primaryInclusion (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    (FGModuleCat.Localization.supportedKMap (nonZeroDivisors R) n).comp
        ((nativePrimaryInclusionExactFunctor R p).KMap n) = primaryAmbientKMap R p n := by
  ext a
  change (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).symm
      (((ObjectProperty.exactInclusion
        (FGModuleCat.Localization.supported (nonZeroDivisors R))).KMap n)
        ((nativePrimaryInclusionExactFunctor R p).KMap n a)) =
    (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).symm
      ((primaryAmbientExactFunctor R p).KMap n a)
  apply congrArg (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).symm
  calc
    _ = ((nativePrimaryInclusionExactFunctor R p).comp (ObjectProperty.exactInclusion
        (FGModuleCat.Localization.supported (nonZeroDivisors R)))).KMap n a :=
      (DFunLike.congr_fun (ExactFunctor.KMap_comp (nativePrimaryInclusionExactFunctor R p)
        (ObjectProperty.exactInclusion
          (FGModuleCat.Localization.supported (nonZeroDivisors R))) n) a).symm
    _ = _ := congrArg (fun f => f.KMap n a)
      (nativePrimaryInclusionExactFunctor_comp_support_inclusion R p)

/-- Sum of the original primary ambient maps into the actual finite-module G-group. -/
def primaryAmbientAssemblyKMap (n : ℕ) :
    (⨁ p, Additive (PrimaryK R p (n + 1))) →+ Additive (FGModuleCat.FractionLocalization.G R (n +
      1)) :=
  DirectSum.toAddMonoid (fun p => (primaryAmbientKMap R p (n + 1)).toAdditive)

set_option maxHeartbeats 800000 in
-- The native supported inclusion unfolds the small-model localization comparison.
/-- The primary assembly retains the original supported inclusion into G-theory. -/
theorem supportedKMap_comp_primaryAssembly (n : ℕ) :
    ((FGModuleCat.Localization.supportedKMap (nonZeroDivisors R) (n + 1)).toAdditive).comp
        ((primaryAssemblyKEquiv R n).toAddMonoidHom : (⨁ p, Additive (PrimaryK R p (n + 1))) →+
          Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) (n + 1))) =
      primaryAmbientAssemblyKMap R n := by
  apply DirectSum.addHom_ext
  intro p a
  change Additive.ofMul (FGModuleCat.Localization.supportedKMap (nonZeroDivisors R) (n + 1)
    (primaryAssemblyKEquiv R n (DirectSum.of _ p a)).toMul) =
      primaryAmbientAssemblyKMap R n (DirectSum.of _ p a)
  rw [primaryAssemblyKEquiv_of, primaryAmbientAssemblyKMap, DirectSum.toAddMonoid_of]
  exact congrArg Additive.ofMul
    (DFunLike.congr_fun (supportedKMap_comp_primaryInclusion R p (n + 1)) a.toMul)

/-- The degree-one native primary assembly, on its original inclusion maps. -/
abbrev primaryK1AssemblyEquiv : (⨁ p, Additive (PrimaryK R p 1)) ≃+
    Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) 1) :=
  primaryAssemblyKEquiv R 0

/-- The degree-two native primary assembly, on its original inclusion maps. -/
abbrev primaryK2AssemblyEquiv : (⨁ p, Additive (PrimaryK R p 2)) ≃+
    Additive (FGModuleCat.Localization.SupportedG (nonZeroDivisors R) 2) :=
  primaryAssemblyKEquiv R 1

end FGModuleCat.DedekindPrimary
