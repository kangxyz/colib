/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.PrimarySupport
public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueDevissage
public import Colib.RingTheory.KTheory.GTheory.Dedekind.Localization
public import Colib.Algebra.Category.FGModuleCat.RestrictScalars
public import Colib.Algebra.Category.FGModuleCat.LocalizationLinear
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Original supported scalar localization at a Dedekind prime

For a Dedekind domain and a height-one prime, the original finite-module
scalar-localization functor restricts to the actual native torsion-support
categories. `supportExactFunctor` and `supportKMap` retain this functor and its
original chosen-zero K-map. Uniform finite-module annihilators prove that the
localized objects remain torsion.

The local maximal ideal gives `localPoint`; its quotient residue type is
literally the original prime's `Ideal.ResidueField`. The local primary
K-evaluation is proved bijective, and `localResidueSupportKEquiv` has precisely
the original local quotient-residue pushforward as its forward map.
`localDvrBoundary` retains the original local finite-module connecting map.

The fraction functor is explicitly `canonicalFractionRestrictionExact`,
restriction along the canonical inverse fraction-ring identification. Its
identification with original generic scalar extension, the two-step module
localization square, and boundary naturality are separate comparisons.
All module and K-theory endpoints use the native common universe `u`.
-/

/-! Implementation source: `Quillen/GTheory/Dedekind/LocalDvrSupport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original maps and hypotheses are retained. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open ModuleCat FGModuleCat
open scoped nonZeroDivisors ModuleCat.Algebra

namespace FGModuleCat.DedekindLocalDvr

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- Actual scalar localization at the prime preserves finite torsion modules. -/
theorem localization_preserves_torsion (M : FGModuleCat.{u} R)
    (h : FGModuleCat.localizationTorsionProperty (nonZeroDivisors R) M) :
    FGModuleCat.localizationTorsionProperty (nonZeroDivisors (Localization.AtPrime p.asIdeal))
      ((FGModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).obj M) := by
  obtain ⟨s, hs⟩ := (Module.Finite.forall_exists_smul_eq_zero_iff (nonZeroDivisors R)).mp h
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
  have hsn : (s : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  let s' : nonZeroDivisors (Localization.AtPrime p.asIdeal) :=
    ⟨algebraMap R (Localization.AtPrime p.asIdeal) s,
      mem_nonZeroDivisors_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr hsn)⟩
  apply (Module.Finite.forall_exists_smul_eq_zero_iff _).mpr
  refine ⟨s', ?_⟩
  change ∀ m : M.obj.localizedModule p.asIdeal.primeCompl,
    (algebraMap R (Localization.AtPrime p.asIdeal) (s : R)) • m = 0
  intro m
  have hm : (s : R) • (𝟙 M) = 0 := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext x
    exact hs x
  have hl : (s : R) • ((FGModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).map
      (𝟙 M)) = 0 := by
    rw [← Functor.map_smul, hm, Functor.map_zero]
  rw [CategoryTheory.Functor.map_id] at hl
  have hl' : (algebraMap R (Localization.AtPrime p.asIdeal) (s : R)) •
      (𝟙 ((FGModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).obj M).obj) = 0 :=
    congrArg (fun f => f.hom) hl
  simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
    LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
    congrArg (fun f => f.hom m) hl'

/-- The original chosen-small-model localization preserves the actual torsion kernel. -/
theorem small_localization_preserves_torsion
    (M : SmallModel.{u} (FGModuleCat.{u} R))
    (h : FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R) M) :
    FGModuleCat.Localization.supported.{u, u}
      (nonZeroDivisors (Localization.AtPrime p.asIdeal))
      (((FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl).smallModel.toFunctor).obj M)
        := by
  apply (FGModuleCat.Localization.supported_iff.{u, u} _ _).mpr
  have hm := localization_preserves_torsion R p
    ((equivSmallModel.{u} (FGModuleCat.{u} R)).inverse.obj M)
    ((FGModuleCat.Localization.supported_iff.{u, u} _ _).mp h)
  exact (FGModuleCat.localizationTorsionProperty (nonZeroDivisors (Localization.AtPrime
    p.asIdeal))).prop_of_iso
    ((equivSmallModel.{u} (FGModuleCat.{u} (Localization.AtPrime p.asIdeal))).unitIso.app
      ((FGModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).obj
        ((equivSmallModel.{u} (FGModuleCat.{u} R)).inverse.obj M))) hm

/-- Restrict the original native scalar-localization functor to the actual support categories. -/
def supportFunctor :
    (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory ⥤
      (FGModuleCat.Localization.supported.{u, u}
        (nonZeroDivisors (Localization.AtPrime p.asIdeal))).FullSubcategory :=
  (FGModuleCat.Localization.supported.{u, u}
    (nonZeroDivisors (Localization.AtPrime p.asIdeal))).lift
      ((FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)).ι ⋙
        (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl).smallModel.toFunctor)
      (fun M => small_localization_preserves_torsion R p M.obj M.property)

instance supportFunctor_additive : (supportFunctor R p).Additive := by
  unfold supportFunctor
  infer_instance

/-- The original restricted scalar-localization functor is exact. -/
def supportExactFunctor : ExactFunctor
    ((abelianExactStructure (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors
      R)).FullSubcategory))
    ((abelianExactStructure (FGModuleCat.Localization.supported.{u, u}
        (nonZeroDivisors (Localization.AtPrime p.asIdeal))).FullSubcategory)) where
  toFunctor := supportFunctor R p
  map_conflation T hT := by
    let P := FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)
    let Q := FGModuleCat.Localization.supported.{u, u}
      (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    have h : ((T.map (supportFunctor R p)).map Q.ι).ShortExact :=
      ((CategoryTheory.SmallModel.mapAbelianExactFunctor (FGModuleCat.localizationExactFunctor
        p.asIdeal.primeCompl))).map_conflation
        (T.map P.ι) ((ObjectProperty.exactInclusion P).map_conflation T hT)
    exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful Q.ι h

/-- The actual support inclusion square is literal at the ordinary functor level. -/
theorem support_comp_inclusion :
    (supportFunctor R p) ⋙
        (FGModuleCat.Localization.supported.{u, u}
          (nonZeroDivisors (Localization.AtPrime p.asIdeal))).ι =
      (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)).ι ⋙
        (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl).smallModel.toFunctor := rfl

/-- Original normalized K-map of the actual supported scalar-localization functor. -/
def supportKMap (n : ℕ) :
    FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n →*
      FGModuleCat.Localization.SupportedG.{u, u}
        (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n :=
  (supportExactFunctor R p).KMap n

/-- The canonical identification of the two actual fraction-ring models. -/
def fractionComparison :
    FractionRing (Localization.AtPrime p.asIdeal) ≃ₐ[Localization.AtPrime p.asIdeal]
      FractionRing R :=
  IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime p.asIdeal)) _ _

/-- The original induced map from the global fraction ring to the local model. -/
def fractionRingMap : FractionRing R →+* FractionRing (Localization.AtPrime p.asIdeal) :=
  (fractionComparison R p).symm.toRingHom

/-- The canonical inverse fraction comparison retains the original R-ring-map square. -/
theorem fractionRingMap_comp :
    (fractionRingMap R p).comp (algebraMap R (FractionRing R)) =
      (algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal))).comp
          (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  ext r
  change (fractionComparison R p).symm (algebraMap R (FractionRing R) r) = _
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal) (FractionRing R) r]
  exact (fractionComparison R p).symm.commutes _

/-- An actual exact functor between fraction-module categories: restriction
along the canonical inverse fraction-ring isomorphism. -/
def canonicalFractionRestrictionExact :
    ExactFunctor ((abelianExactStructure (FGModuleCat.{u} (FractionRing R))))
      ((abelianExactStructure (FGModuleCat.{u} (FractionRing (Localization.AtPrime p.asIdeal))))) :=
  FGModuleCat.finiteRestrictionExact
    (fractionComparison R p).toRingHom
    (RingHom.Finite.of_surjective _ (fractionComparison R p).surjective)

/-- Original small K-map of canonical fraction restriction, before scalar-extension comparison. -/
def canonicalFractionRestrictionKMap (n : ℕ) :
    FGModuleCat.FractionLocalization.G.{u, u} (FractionRing R) n →*
      FGModuleCat.FractionLocalization.G.{u, u} (FractionRing (Localization.AtPrime p.asIdeal)) n :=
  (canonicalFractionRestrictionExact R p).smallKMap n

/-- The unique nonzero local prime, represented by the actual local maximal ideal. -/
def localPoint : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime p.asIdeal) where
  asIdeal := IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)
  isPrime := (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal _)
    (IsLocalization.AtPrime.not_isField R p.ne_bot (Localization.AtPrime p.asIdeal))

/-- The local quotient residue type is literally the global prime's native
`Ideal.ResidueField`; no extra choice of a residue-field isomorphism is needed. -/
theorem localResidueQuotient_eq :
    (Localization.AtPrime p.asIdeal ⧸ (localPoint R p).asIdeal) = p.asIdeal.ResidueField := rfl

/-- The actual local quotient-residue devissage has the already prescribed
native global prime residue field as its source. -/
def localResiduePrimaryKEquiv (n : ℕ) :
    FGModuleCat.FractionLocalization.G.{u, u} p.asIdeal.ResidueField n ≃*
      DedekindPrimary.PrimaryK (Localization.AtPrime p.asIdeal) (localPoint R p) n :=
  DedekindResidue.residuePrimaryKEquiv (Localization.AtPrime p.asIdeal) (localPoint R p) n

/-- Every nonzero local prime is the actual maximal ideal. -/
theorem localPoint_unique
    (q : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime p.asIdeal)) :
    q = localPoint R p :=
  IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal q.isMaximal)

/-- The original local primary-evaluation K-map is bijective in every degree. -/
theorem localPrimaryEvaluation_bijective (n : ℕ) :
    Function.Bijective ((DedekindPrimary.primaryEvaluationExactFunctor
      (Localization.AtPrime p.asIdeal) (localPoint R p)).KMap n) := by
  constructor
  · intro a b h
    apply DedekindPrimary.supportedK_ext (Localization.AtPrime p.asIdeal) n
    intro q
    have hq := localPoint_unique R p q
    subst q
    exact h
  · intro a
    refine ⟨(FGModuleCat.PrimaryDecomposition.nativePrimaryInclusionExactFunctor
      (Localization.AtPrime p.asIdeal) (localPoint R p)).KMap n a, ?_⟩
    exact DFunLike.congr_fun (DedekindPrimary.primaryEvaluationKMap_comp_inclusion
      (Localization.AtPrime p.asIdeal) n (localPoint R p)) a

/-- The actual local primary-evaluation K-map, bundled with its proved inverse. -/
def localPrimaryEvaluationKEquiv (n : ℕ) :
    FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors (Localization.AtPrime p.asIdeal))
      n ≃*
      DedekindPrimary.PrimaryK (Localization.AtPrime p.asIdeal) (localPoint R p) n :=
  MulEquiv.ofBijective ((DedekindPrimary.primaryEvaluationExactFunctor
    (Localization.AtPrime p.asIdeal) (localPoint R p)).KMap n)
      (localPrimaryEvaluation_bijective R p n)

/-- The proved local primary/residue identification of the actual support group. -/
def localResidueSupportKEquiv (n : ℕ) :
    FGModuleCat.FractionLocalization.G.{u, u} p.asIdeal.ResidueField n ≃*
      FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors (Localization.AtPrime
        p.asIdeal)) n :=
  (localResiduePrimaryKEquiv R p n).trans (localPrimaryEvaluationKEquiv R p n).symm

/-- The local support equivalence has the original local quotient-residue pushforward forward. -/
theorem localResidueSupportKEquiv_apply (n : ℕ)
    (a : FGModuleCat.FractionLocalization.G.{u, u} p.asIdeal.ResidueField n) :
    localResidueSupportKEquiv R p n a =
      DedekindResidue.quotientResidueSupportKMap
        (Localization.AtPrime p.asIdeal) (localPoint R p) n a := by
  apply (localPrimaryEvaluationKEquiv R p n).injective
  change localPrimaryEvaluationKEquiv R p n
      ((localPrimaryEvaluationKEquiv R p n).symm (localResiduePrimaryKEquiv R p n a)) = _
  rw [MulEquiv.apply_symm_apply, DedekindResidue.quotientResidueSupportKMap_eq]
  have h := DFunLike.congr_fun (DedekindPrimary.primaryEvaluationKMap_comp_inclusion
    (Localization.AtPrime p.asIdeal) n (localPoint R p))
      ((DedekindResidue.residueToPrimaryExact
        (Localization.AtPrime p.asIdeal) (localPoint R p)).KMap n a)
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h
  have he : localResiduePrimaryKEquiv R p n a =
      (DedekindResidue.residueToPrimaryExact
        (Localization.AtPrime p.asIdeal) (localPoint R p)).KMap n a :=
    DFunLike.congr_fun (DedekindResidue.residuePrimaryKEquiv_toMonoidHom
      (Localization.AtPrime p.asIdeal) (localPoint R p) n) a
  exact he.trans h.symm

/-- The actual local finite-module boundary followed by its proved local
quotient-residue devissage. This is not identified with the global coordinate here. -/
def localDvrBoundary (n : ℕ) :
    FGModuleCat.FractionLocalization.G.{u, u} (FractionRing (Localization.AtPrime p.asIdeal)) (n
      + 1) →*
      FGModuleCat.FractionLocalization.G.{u, u} p.asIdeal.ResidueField n :=
  (localResidueSupportKEquiv R p n).symm.toMonoidHom.comp
    (FGModuleCat.Localization.connectingHom.{u, u}
      (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n)

end FGModuleCat.DedekindLocalDvr
