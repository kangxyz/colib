/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.LocalDvrSupport
public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueFieldAssembly
public import Colib.RingTheory.KTheory.Quillen.Field.ScalarExtensionComparison
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Canonical module comparisons for localization at a Dedekind prime

The actual two-step finite-module localizations compare by their tensor
universal properties. Canonical inverse fraction-ring restriction is naturally
isomorphic to the original scalar-extension functor; the inverse comparison
retains the original tensor unit. The resulting square therefore identifies
original normalized small-model K-maps in every degree.

The original chosen-prime residue pushforward localizes to the original local
quotient-residue pushforward. Other residue pushforwards are naturally zero.
Canonical model units and ordinary full-subcategory inclusions prove these
comparisons before passing to K-theory. The original positive-degree residue
assembly therefore computes exactly the chosen-prime support coordinate.

All module carriers and K-theory endpoints use the native common universe `u`.
Canonical Serre fiber comparison and boundary naturality belong to their
separate owning sources.
-/

/-! Implementation source: `Quillen/GTheory/Dedekind/LocalDvrComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original maps and hypotheses are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open ModuleCat FGModuleCat
open scoped nonZeroDivisors TensorProduct ChangeOfRings

namespace FGModuleCat.DedekindLocalDvr

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [CommRing A] (S : Submonoid A)

/-- The coefficient identity compares the explicit restricted and canonical scalar actions. -/
def tensorCoefficientEquiv :
    (ModuleCat.restrictScalars (algebraMap A (Localization S))).obj
        (ModuleCat.of (Localization S) (Localization S)) ≃ₗ[A] Localization S :=
  { AddEquiv.refl _ with
    map_smul' := by
      intro r s
      change (algebraMap A (Localization S) r) * (show Localization S from s) =
        r • (show Localization S from s)
      exact (Algebra.smul_def r (show Localization S from s)).symm }

/-- Scalar extension's actual coefficient action agrees with the canonical localization action. -/
def extensionTensorEquiv (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A (Localization S))).obj M ≃ₗ[Localization S]
      Localization S ⊗[A] M :=
  { (TensorProduct.congr (tensorCoefficientEquiv S) (LinearEquiv.refl A M)).toAddEquiv with
    map_smul' := by
      intro r x
      change (TensorProduct.congr (tensorCoefficientEquiv S) (LinearEquiv.refl A M))
          (r • x) = r •
        (TensorProduct.congr (tensorCoefficientEquiv S) (LinearEquiv.refl A M)) x
      refine TensorProduct.inductionOn x ?_ ?_
      · intro s m
        simp only [TensorProduct.smul_tmul', TensorProduct.congr_tmul]
        rfl
      · intro x y hx hy
        simp only [smul_add, map_add, hx, hy] }

private theorem extensionTensorEquiv_tmul (M : ModuleCat.{u} A) (s : Localization S) (m : M) :
    extensionTensorEquiv S M (s ⊗ₜ[A,algebraMap A (Localization S)] m) = s ⊗ₜ[A] m := by
  exact TensorProduct.congr_tmul _ _ _ _

/-- The tensor universal property compares the actual localized-module object. -/
def localizationTensorIsoApp (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A (Localization S))).obj M ≅ M.localizedModule S :=
  (extensionTensorEquiv S M).toModuleIso ≪≫
    (IsLocalizedModule.isBaseChange S (Localization S)
      (M.localizedModuleMkLinearMap S)).equiv.toModuleIso

private theorem localizationTensorIsoApp_unit (M : ModuleCat.{u} A) (m : M) :
    (localizationTensorIsoApp S M).hom
        ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m) =
      M.localizedModuleMkLinearMap S m := by
  dsimp only [localizationTensorIsoApp, Iso.trans_hom]
  rw [ModuleCat.comp_apply]
  change (IsLocalizedModule.isBaseChange S (Localization S)
    (M.localizedModuleMkLinearMap S)).equiv (extensionTensorEquiv S M
      ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m)) = _
  rw [extensionTensorEquiv_tmul, IsBaseChange.equiv_tmul, one_smul]

attribute [irreducible] localizationTensorIsoApp

set_option backward.isDefEq.respectTransparency true in
/-- Tensor extension and the original module-localization functor are canonically isomorphic. -/
def localizationTensorIso :
    ModuleCat.extendScalars (algebraMap A (Localization S)) ≅
      ModuleCat.localizedModuleFunctor.{u} S :=
  NatIso.ofComponents
    (F := ModuleCat.extendScalars (algebraMap A (Localization S)))
    (G := ModuleCat.localizedModuleFunctor.{u} S)
    (fun (M : ModuleCat.{u} A) => localizationTensorIsoApp S M) (by
    intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (localizationTensorIsoApp S N).hom
        ((ModuleCat.extendScalars (algebraMap A (Localization S))).map f
          ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m)) =
      (ModuleCat.localizedModuleMap S f) ((localizationTensorIsoApp S M).hom
        ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m))
    erw [ModuleCat.ExtendScalars.map_tmul, localizationTensorIsoApp_unit,
      localizationTensorIsoApp_unit]
    exact (IsLocalizedModule.map_apply S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) f.hom m).symm)

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- Canonical fraction restriction agrees with original scalar extension
along the inverse ring map. -/
def fractionRestrictionModuleIso :
    ModuleCat.restrictScalars (fractionComparison R p).toRingHom ≅
      ModuleCat.extendScalars (fractionRingMap R p) :=
  Adjunction.leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (fractionComparison R p).toRingEquiv).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj (fractionRingMap R p))

/-- The inverse comparison takes the original tensor unit to the same module element. -/
theorem fractionRestrictionModuleIso_inv_unit (M : ModuleCat.{u} (FractionRing R)) (m : M) :
    (fractionRestrictionModuleIso R p).inv.app M
        ((1 : FractionRing (Localization.AtPrime p.asIdeal)) ⊗ₜ[FractionRing R,fractionRingMap R p]
          m) =
      m := by
  rw [fractionRestrictionModuleIso, Adjunction.leftAdjointUniq_inv_app]
  change (ModuleCat.extendRestrictScalarsAdj (fractionRingMap R p)).homEquiv _ _
    ((Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj (fractionRingMap R p))
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (fractionComparison R p).toRingEquiv).toAdjunction).hom.app M) m = m
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

/-- The canonical restriction and original tensor extension agree on actual finite modules. -/
def fractionRestrictionExtensionIso :
    (canonicalFractionRestrictionExact R p).toFunctor ≅
      (FGModuleCat.finiteModuleExtensionExact (fractionRingMap R p)).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((fractionRestrictionModuleIso R p).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (fractionRestrictionModuleIso R p).hom.naturality f.hom)

/-- Canonical fraction restriction retains the original generic scalar-extension K-map. -/
theorem canonicalFractionRestrictionKMap_eq_extension (n : ℕ) :
    canonicalFractionRestrictionKMap R p n =
      (FGModuleCat.finiteModuleExtensionExact (fractionRingMap R p)).smallKMap n :=
  ExactFunctor.smallKMap_eq_of_natIso (fractionRestrictionExtensionIso R p) n

/-- Actual module-localization comparison via the two canonical tensor universal properties. -/
def fractionLocalizationModuleIso :
    ModuleCat.localizedModuleFunctor (nonZeroDivisors R) ⋙
        ModuleCat.restrictScalars (fractionComparison R p).toRingHom ≅
      ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl ⋙
        ModuleCat.localizedModuleFunctor (nonZeroDivisors (Localization.AtPrime p.asIdeal)) :=
  Functor.isoWhiskerRight (localizationTensorIso (nonZeroDivisors R)).symm
      (ModuleCat.restrictScalars (fractionComparison R p).toRingHom) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars (algebraMap R (FractionRing R)))
      (fractionRestrictionModuleIso R p) ≪≫
    (ModuleCat.extendScalarsComp (algebraMap R (FractionRing R)) (fractionRingMap R p)).symm ≪≫
    eqToIso (congrArg (fun f : R →+* FractionRing (Localization.AtPrime p.asIdeal) =>
      ModuleCat.extendScalars.{u} f) (fractionRingMap_comp R p)) ≪≫
    ModuleCat.extendScalarsComp (algebraMap R (Localization.AtPrime p.asIdeal))
      (algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal))) ≪≫
    Functor.isoWhiskerRight (localizationTensorIso p.asIdeal.primeCompl)
      (ModuleCat.extendScalars (algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal)))) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
      (localizationTensorIso (nonZeroDivisors (Localization.AtPrime p.asIdeal)))

/-- The two prescribed finite-module localization composites are canonically
naturally isomorphic. -/
def fractionLocalizationComparison :
    ((FGModuleCat.localizationExactFunctor (nonZeroDivisors R)).comp
      (canonicalFractionRestrictionExact R p)).toFunctor ≅
    ((FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl).comp
      (FGModuleCat.localizationExactFunctor
        (nonZeroDivisors (Localization.AtPrime p.asIdeal)))).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((fractionLocalizationModuleIso R p).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (fractionLocalizationModuleIso R p).hom.naturality f.hom)

/-- The actual two-step localization square retains all original small-model K-maps. -/
theorem fractionLocalizationKMap_square (n : ℕ) :
    (canonicalFractionRestrictionKMap R p n).comp
        (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) n) =
      (FGModuleCat.Localization.localizationKMap.{u, u}
        (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n).comp
          (FGModuleCat.Localization.localizationKMap.{u, u} p.asIdeal.primeCompl n) := by
  rw [canonicalFractionRestrictionKMap, FGModuleCat.Localization.localizationKMap,
    FGModuleCat.Localization.localizationKMap,
    FGModuleCat.Localization.localizationKMap,
    ← ExactFunctor.smallKMap_comp, ← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso (fractionLocalizationComparison R p) n

/-- A residue pushforward at another prime vanishes under the actual localization functor. -/
theorem residueFieldPushforward_localization_isZero
    (q : IsDedekindDomain.HeightOneSpectrum R) (hqp : q ≠ p)
    (M : FGModuleCat.{u} q.asIdeal.ResidueField) :
    IsZero ((FGModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).obj
      ((DedekindResidue.residueFieldPushforwardExact R q).toFunctor.obj M)) := by
  have hnot : ¬ q.asIdeal ≤ p.asIdeal := by
    intro h
    exact hqp (IsDedekindDomain.HeightOneSpectrum.ext
      (q.isMaximal.eq_of_le p.isPrime.ne_top h))
  obtain ⟨r, hrq, hrp⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  change (FGModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).kernel _
  rw [FGModuleCat.localizedModuleFunctor_kernel]
  apply (Module.Finite.forall_exists_smul_eq_zero_iff p.asIdeal.primeCompl).mpr
  refine ⟨⟨r, hrp⟩, fun m => ?_⟩
  change (algebraMap R q.asIdeal.ResidueField r) • (show M from m) = 0
  rw [Ideal.algebraMap_residueField_eq_zero.mpr hrq, zero_smul]

end FGModuleCat.DedekindLocalDvr

open FGModuleCat.PrimaryDecomposition
open FGModuleCat.IdealSupport
open scoped DirectSum

namespace FGModuleCat.DedekindLocalDvr

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

section AlreadyLocalized
variable {A : Type u} [CommRing A] (S : Submonoid A)

local notation "resUnit" N => ModuleCat.localizedModuleMkLinearMap
  (Functor.obj (ModuleCat.restrictScalars (algebraMap A (Localization S))) N) S

/-- The original localization unit is an isomorphism for a module over the localized ring. -/
def alreadyLocalizedEquiv (N : ModuleCat.{u} (Localization S)) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj N).localizedModule S
      ≃ₗ[Localization S] N := by
  let N₀ := (ModuleCat.restrictScalars (algebraMap A (Localization S))).obj N
  have : IsScalarTower A (Localization S) N₀ :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule S (LinearMap.id : N₀ →ₗ[A] N₀) :=
    isLocalizedModule_id S N₀ (Localization S)
  exact (IsLocalizedModule.linearEquiv S (N₀.localizedModuleMkLinearMap S)
    (LinearMap.id : N₀ →ₗ[A] N₀)).extendScalarsOfIsLocalization S (Localization S)

/-- The comparison retains each element along the actual localization unit. -/
theorem alreadyLocalizedEquiv_unit (N : ModuleCat.{u} (Localization S)) (m : N) :
    alreadyLocalizedEquiv S N
      ((resUnit N) m) = m := by
  let : Module A N := Module.compHom N (algebraMap A (Localization S))
  have : IsScalarTower A (Localization S) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule S (LinearMap.id : N →ₗ[A] N) :=
    isLocalizedModule_id S N (Localization S)
  unfold alreadyLocalizedEquiv
  change IsLocalizedModule.linearEquiv S
    ((resUnit N))
    (LinearMap.id : N →ₗ[A] N)
      (((resUnit N)) m) = m
  exact IsLocalizedModule.linearEquiv_apply S _ _ m

/-- The canonical comparison for an already localized module, as an actual module isomorphism. -/
def alreadyLocalizedIsoApp (N : ModuleCat.{u} (Localization S)) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization S))).obj N).localizedModule S ≅ N :=
  (alreadyLocalizedEquiv S N).toModuleIso

/-- Restriction and localization return the same original localized-ring module naturally. -/
def alreadyLocalizedIso :
    ModuleCat.restrictScalars (algebraMap A (Localization S)) ⋙
      ModuleCat.localizedModuleFunctor S ≅ 𝟭 (ModuleCat.{u} (Localization S)) :=
  NatIso.ofComponents (fun N => alreadyLocalizedIsoApp S N) (by
    intro N N' f
    let : Module A N := Module.compHom N (algebraMap A (Localization S))
    let : Module A N' := Module.compHom N' (algebraMap A (Localization S))
    have : IsScalarTower A (Localization S) N :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower A (Localization S) N' :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsLocalizedModule S (LinearMap.id : N' →ₗ[A] N') :=
      isLocalizedModule_id S N' (Localization S)
    apply ModuleCat.hom_ext
    change (ModuleCat.localizedModuleMap S ((ModuleCat.restrictScalars
        (algebraMap A (Localization S))).map f) ≫ (alreadyLocalizedIsoApp S N').hom).hom =
      ((alreadyLocalizedIsoApp S N).hom ≫ f).hom
    apply LinearMap.restrictScalars_injective A
    apply IsLocalizedModule.ext S
      ((resUnit N))
      (IsLocalizedModule.map_units (LinearMap.id : N' →ₗ[A] N'))
    ext m
    change alreadyLocalizedEquiv S N'
        ((ModuleCat.localizedModuleMap S ((ModuleCat.restrictScalars
          (algebraMap A (Localization S))).map f))
            ((resUnit N) m)) =
      f (alreadyLocalizedEquiv S N
        ((resUnit N) m))
    rw [alreadyLocalizedEquiv_unit]
    change alreadyLocalizedEquiv S N'
      (IsLocalizedModule.map S
        ((resUnit N))
        ((resUnit N'))
        ((ModuleCat.restrictScalars (algebraMap A (Localization S))).map f).hom
        (((resUnit N))
          m)) = f m
    rw [IsLocalizedModule.map_apply, alreadyLocalizedEquiv_unit]
    rfl)

end AlreadyLocalized

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- Actual residue-module localization agrees with the original local quotient restriction. -/
def residueLocalizationModuleIso :
    ModuleCat.restrictScalars (algebraMap R p.asIdeal.ResidueField) ⋙
        ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl ≅
      ModuleCat.restrictScalars (Ideal.Quotient.mk (localPoint R p).asIdeal) :=
  Functor.isoWhiskerRight
    (ModuleCat.restrictScalarsComp' (algebraMap R (Localization.AtPrime p.asIdeal))
      (Ideal.Quotient.mk (localPoint R p).asIdeal) (algebraMap R p.asIdeal.ResidueField) (by
        ext r
        rfl)) (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars
      (Ideal.Quotient.mk (localPoint R p).asIdeal))
      (alreadyLocalizedIso p.asIdeal.primeCompl) ≪≫
    Functor.rightUnitor _

/-- The chosen-prime residue pushforward and localization compare on actual finite modules. -/
def residueLocalizationComparison :
    ((DedekindResidue.residueFieldPushforwardExact R p).comp
      (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl)).toFunctor ≅
      (FGModuleCat.IdealSupport.closedRestrictionExact
        (localPoint R p).asIdeal).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((residueLocalizationModuleIso R p).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (residueLocalizationModuleIso R p).hom.naturality f.hom)

/-- The original quotient support functor retains its ambient restriction after canonical model
units. -/
def quotientResidueSupportInclusionIso :
    (DedekindResidue.quotientResidueSupportExactFunctor R p).toFunctor ⋙
        (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)).ι ≅
      (closedRestrictionExact p.asIdeal).smallModel.toFunctor := by
  let Q := equivSmallModel.{u} (FGModuleCat.{u} (R ⧸ p.asIdeal))
  let e := equivSmallModel.{u} (PrimaryModule R p.asIdeal)
  let A := equivSmallModel.{u} (FGModuleCat.{u} R)
  let H := Q.inverse ⋙ DedekindResidue.quotientToPrimary R p
  let K := (primaryObjectProperty R p.asIdeal).ι ⋙ A.functor
  change H ⋙ e.functor ⋙ e.inverse ⋙ K ≅ H ⋙ K
  exact Functor.isoWhiskerLeft H (Functor.isoWhiskerRight e.unitIso.symm K) ≪≫
    Functor.isoWhiskerLeft H (Functor.leftUnitor K)

/-- The native residue support functor retains the original ambient field restriction. -/
def residueFieldSupportInclusionIso (q : IsDedekindDomain.HeightOneSpectrum R) :
    (DedekindResidue.residueFieldSupportExactFunctor R q).toFunctor ⋙
        (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)).ι ≅
      (DedekindResidue.residueFieldPushforwardExact R q).smallModel.toFunctor :=
  Functor.isoWhiskerLeft (DedekindResidue.residueFieldRestrictionExact R q).smallModel.toFunctor
    (quotientResidueSupportInclusionIso R q) ≪≫
      DedekindResidue.residueFieldSmallRestrictionPushforwardIso R q

/-- Actual support localization retains the original ambient composite of finite-module functors. -/
def localizedResidueSupportInclusionIso (q : IsDedekindDomain.HeightOneSpectrum R) :
    ((DedekindResidue.residueFieldSupportExactFunctor R q).comp
        (supportExactFunctor R p)).toFunctor ⋙
          (FGModuleCat.Localization.supported.{u, u}
            (nonZeroDivisors (Localization.AtPrime p.asIdeal))).ι ≅
      ((DedekindResidue.residueFieldPushforwardExact R q).comp
        (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl)).smallModel.toFunctor := by
  change ((DedekindResidue.residueFieldSupportExactFunctor R q).toFunctor ⋙
      (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors R)).ι) ⋙
        (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl).smallModel.toFunctor ≅ _
  exact Functor.isoWhiskerRight (residueFieldSupportInclusionIso R q)
      (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl).smallModel.toFunctor ≪≫
    (ExactFunctor.smallModelCompIso (DedekindResidue.residueFieldPushforwardExact R q)
      (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl)).symm

/-- The original residue-support pushforward localizes to the original local quotient-support
functor. -/
def residueSupportLocalizationComparison :
    ((DedekindResidue.residueFieldSupportExactFunctor R p).comp
      (supportExactFunctor R p)).toFunctor ≅
        (DedekindResidue.quotientResidueSupportExactFunctor
          (Localization.AtPrime p.asIdeal) (localPoint R p)).toFunctor := by
  let Q := FGModuleCat.Localization.supported.{u, u}
    (nonZeroDivisors (Localization.AtPrime p.asIdeal))
  let e := localizedResidueSupportInclusionIso R p p ≪≫
    ExactFunctor.smallModelNatIso (residueLocalizationComparison R p) ≪≫
      (quotientResidueSupportInclusionIso (Localization.AtPrime p.asIdeal) (localPoint R p)).symm
  exact (Q.fullyFaithfulι.whiskeringRight _).preimageIso e

/-- The chosen-prime original support map is exactly the original local residue pushforward. -/
theorem supportKMap_comp_residueFieldSupport (n : ℕ) :
    (supportKMap R p n).comp (DedekindResidue.residueFieldSupportKMap R p n) =
      (localResidueSupportKEquiv R p n).toMonoidHom := by
  calc
    _ = ((DedekindResidue.residueFieldSupportExactFunctor R p).comp
        (supportExactFunctor R p)).KMap n := (ExactFunctor.KMap_comp _ _ n).symm
    _ = (DedekindResidue.quotientResidueSupportExactFunctor
        (Localization.AtPrime p.asIdeal) (localPoint R p)).KMap n :=
      ExactFunctor.KMap_eq_of_natIso (residueSupportLocalizationComparison R p) n
    _ = _ := by
      ext a
      exact (localResidueSupportKEquiv_apply R p n a).symm

/-- A residue object at another prime becomes an actual zero object in the local support
category. -/
theorem localizedOtherResidueSupport_isZero
    (q : IsDedekindDomain.HeightOneSpectrum R) (hqp : q ≠ p)
    (M : SmallModel.{u} (FGModuleCat.{u} q.asIdeal.ResidueField)) :
    IsZero (((DedekindResidue.residueFieldSupportExactFunctor R q).comp
      (supportExactFunctor R p)).toFunctor.obj M) := by
  let Q := FGModuleCat.Localization.supported.{u, u}
    (nonZeroDivisors (Localization.AtPrime p.asIdeal))
  let L := (DedekindResidue.residueFieldPushforwardExact R q).comp
    (FGModuleCat.localizationExactFunctor p.asIdeal.primeCompl)
  let X := (equivSmallModel.{u} (FGModuleCat.{u} q.asIdeal.ResidueField)).inverse.obj M
  have hz := residueFieldPushforward_localization_isZero R p q hqp X
  have hsmall : IsZero (L.smallModel.toFunctor.obj M) :=
    (equivSmallModel.{u} (FGModuleCat.{u} (Localization.AtPrime p.asIdeal))).functor.map_isZero hz
  have hambient : IsZero (Q.ι.obj (((DedekindResidue.residueFieldSupportExactFunctor R q).comp
      (supportExactFunctor R p)).toFunctor.obj M)) :=
    hsmall.of_iso ((localizedResidueSupportInclusionIso R p q).app M)
  exact IsZero.of_full_of_faithful_of_isZero Q.ι _ hambient

/-- Off-point support localization is naturally isomorphic to the actual chosen-zero exact
functor. -/
def localizedOtherResidueSupportIsoZero
    (q : IsDedekindDomain.HeightOneSpectrum R) (hqp : q ≠ p) :
    ((DedekindResidue.residueFieldSupportExactFunctor R q).comp
      (supportExactFunctor R p)).toFunctor ≅
      (ExactFunctor.zero
        ((abelianExactStructure (FGModuleCat.{u} q.asIdeal.ResidueField))).smallModel
        ((abelianExactStructure (FGModuleCat.Localization.supported.{u, u}
          (nonZeroDivisors (Localization.AtPrime p.asIdeal))).FullSubcategory))).toFunctor :=
  NatIso.ofComponents (fun M => (localizedOtherResidueSupport_isZero R p q hqp M).iso
    (isZero_zero _)) (by
      intro X Y f
      exact (localizedOtherResidueSupport_isZero R p q hqp X).eq_of_src _ _)

/-- Every original off-point residue-support K-map becomes trivial under actual support
localization. -/
theorem supportKMap_comp_residueFieldSupport_of_ne
    (q : IsDedekindDomain.HeightOneSpectrum R) (hqp : q ≠ p) (n : ℕ) :
    (supportKMap R p n).comp (DedekindResidue.residueFieldSupportKMap R q n) = 1 := by
  calc
    _ = ((DedekindResidue.residueFieldSupportExactFunctor R q).comp
        (supportExactFunctor R p)).KMap n := (ExactFunctor.KMap_comp _ _ n).symm
    _ = (ExactFunctor.zero
        ((abelianExactStructure (FGModuleCat.{u} q.asIdeal.ResidueField))).smallModel
        ((abelianExactStructure (FGModuleCat.Localization.supported.{u, u}
          (nonZeroDivisors (Localization.AtPrime p.asIdeal))).FullSubcategory))).KMap n :=
      ExactFunctor.KMap_eq_of_natIso (localizedOtherResidueSupportIsoZero R p q hqp) n
    _ = 1 := ExactFunctor.KMap_zero _ _ n

/-- The original residue assembly localizes to its chosen-prime coordinate in every positive
degree. -/
theorem supportKMap_residueFieldAssembly (n : ℕ)
    (a : ⨁ q, Additive (DedekindResidue.ResidueFieldK R q (n + 1))) :
    Additive.ofMul (supportKMap R p (n + 1)
      (DedekindResidue.residueFieldAssemblyKEquiv R n a).toMul) =
      Additive.ofMul (localResidueSupportKEquiv R p (n + 1) (a p).toMul) := by
  calc
    _ = ∑ q ∈ a.support, Additive.ofMul (supportKMap R p (n + 1)
        (DedekindResidue.residueFieldSupportKMap R q (n + 1) (a q).toMul)) := by
      change ((supportKMap R p (n + 1)).toAdditive)
        (DedekindResidue.residueFieldAssemblyKEquiv R n a) = _
      rw [DedekindResidue.residueFieldAssemblyKEquiv_eq_sum, map_sum]
      rfl
    _ = Additive.ofMul (supportKMap R p (n + 1)
        (DedekindResidue.residueFieldSupportKMap R p (n + 1) (a p).toMul)) := by
      apply Finset.sum_eq_single p
      · intro q hq hqp
        have hz := DFunLike.congr_fun
          (supportKMap_comp_residueFieldSupport_of_ne R p q hqp (n + 1)) (a q).toMul
        change supportKMap R p (n + 1)
          (DedekindResidue.residueFieldSupportKMap R q (n + 1) (a q).toMul) = 1 at hz
        exact congrArg Additive.ofMul hz
      · intro hp
        have ha : a p = 0 := DFinsupp.notMem_support_iff.mp hp
        simp [ha]
    _ = _ := by
      have h := DFunLike.congr_fun (supportKMap_comp_residueFieldSupport R p (n + 1)) (a p).toMul
      change supportKMap R p (n + 1)
        (DedekindResidue.residueFieldSupportKMap R p (n + 1) (a p).toMul) =
        localResidueSupportKEquiv R p (n + 1) (a p).toMul at h
      exact congrArg Additive.ofMul h

/-- The proved local residue equivalence identifies the actual localized assembly with its
coordinate. -/
theorem localResidueSupportCoordinate (n : ℕ)
    (a : ⨁ q, Additive (DedekindResidue.ResidueFieldK R q (n + 1))) :
    (localResidueSupportKEquiv R p (n + 1)).symm
      (supportKMap R p (n + 1) (DedekindResidue.residueFieldAssemblyKEquiv R n a).toMul) =
      (a p).toMul := by
  apply (localResidueSupportKEquiv R p (n + 1)).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg Additive.toMul (supportKMap_residueFieldAssembly R p n a)
  simpa only [toMul_ofMul] using h

end FGModuleCat.DedekindLocalDvr
