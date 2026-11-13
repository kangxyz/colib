/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.LocalDvrBoundaryNaturality
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.PrincipalClosedLocalization
public import Colib.Algebra.Category.ModuleCat.LocalizationTensor
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Principal finite-module boundaries and the actual local-DVR boundary

The prescribed principal-open fraction equivalence and quotient-residue
isomorphism intertwine the original finite-module connecting maps in every
degree. The proof retains the actual scalar restrictions and the original
supported functor square. Scheme boundary comparison is a separate consumer.

Implementation source: `Quillen/GTheory/Dedekind/PrincipalDvrBoundaryComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, through `principalBoundary_nativeBoundary`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat FGModuleCat
open scoped nonZeroDivisors

namespace FGModuleCat.DedekindLocalDvr.PrincipalComparison
attribute [local instance] Abelian.hasFiniteBiproducts
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (S T : Submonoid R) (e : Localization S ≃ₐ[R] Localization T)

private def targetExact := FGModuleCat.finiteRestrictionExact.{u, u, u}
  e.symm.toRingHom (RingHom.Finite.of_surjective _ e.symm.surjective)

private def restrictionExtensionIso :
    ModuleCat.restrictScalars e.symm.toRingHom ≅ ModuleCat.extendScalars e.toRingHom :=
  Adjunction.leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm.toRingEquiv).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom)

private def moduleIso :
    ModuleCat.localizedModuleFunctor S ⋙ ModuleCat.restrictScalars e.symm.toRingHom ≅
      ModuleCat.localizedModuleFunctor T :=
  Functor.isoWhiskerRight (localizationTensorIso S).symm
      (ModuleCat.restrictScalars e.symm.toRingHom) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars (algebraMap R (Localization S)))
      (restrictionExtensionIso S T e) ≪≫
    (ModuleCat.extendScalarsComp (algebraMap R (Localization S)) e.toRingHom).symm ≪≫
    eqToIso (congrArg (fun f : R →+* Localization T => ModuleCat.extendScalars.{u} f)
      (by ext r; exact e.commutes r)) ≪≫
    localizationTensorIso T

private def ordinarySquare :
    ((FGModuleCat.localizationExactFunctor.{u, u} S).comp (targetExact S T e)).toFunctor ≅
    ((ExactFunctor.id (abelianExactStructure (FGModuleCat.{u} R))).comp
      (FGModuleCat.localizationExactFunctor.{u, u} T)).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ((moduleIso S T e).app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact (moduleIso S T e).hom.naturality f.hom)

private def supportExact := FGModuleCat.Localization.inducedSupportedExactFunctorOfSquare S T
  (ExactFunctor.id (abelianExactStructure (FGModuleCat.{u} R)))
  (targetExact S T e) (ordinarySquare S T e)

private theorem connectingHom_square (n : ℕ) :
    ((supportExact S T e).KMap n).comp (FGModuleCat.Localization.connectingHom S n) =
      (FGModuleCat.Localization.connectingHom T n).comp ((targetExact S T e).smallKMap.{u}
        (n + 1)) :=
  FGModuleCat.Localization.connectingHom_naturality S T
    (ExactFunctor.id (abelianExactStructure (FGModuleCat.{u} R)))
    (targetExact S T e) (ordinarySquare S T e) n
end FGModuleCat.DedekindLocalDvr.PrincipalComparison


namespace FGModuleCat.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local instance : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _
variable {π : (Localization.AtPrime p.asIdeal)} (hπ : Irreducible π)
include hπ

/-- The native fraction ring is the actual localization away from the chosen irreducible. -/
theorem principalFraction_isLocalizationAway :
    IsLocalization.Away π (FractionRing (Localization.AtPrime p.asIdeal)) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := FractionRing (Localization.AtPrime p.asIdeal))
    (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
  · infer_instance
  · intro a ha
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp ha) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

/-- The canonical algebra equivalence from the actual principal open to the native fraction ring. -/
def principalAwayFractionEquiv :
    Localization.Away π ≃ₐ[Localization.AtPrime p.asIdeal]
      FractionRing (Localization.AtPrime p.asIdeal) :=
  letI := principalFraction_isLocalizationAway R p hπ
  IsLocalization.algEquiv (Submonoid.powers π) _ _

/-- The actual principal quotient identifies with the prescribed local residue field. -/
def principalClosedResidueEquiv :
    FGModuleCat.ClosedRing π ≃+* p.asIdeal.ResidueField :=
  Ideal.quotEquivOfEq hπ.maximalIdeal_eq.symm

/-- Actual scalar restriction along the inverse of the prescribed quotient-residue equivalence. -/
def principalResidueRestrictionExact := FGModuleCat.finiteRestrictionExact.{u, u, u}
  (principalClosedResidueEquiv R p hπ).symm.toRingHom
  (RingHom.Finite.of_surjective _ (principalClosedResidueEquiv R p hπ).symm.surjective)

/-- Actual scalar restriction along the inverse canonical principal-open fraction equivalence. -/
def principalFractionRestrictionExact := FGModuleCat.finiteRestrictionExact.{u, u, u}
  (principalAwayFractionEquiv R p hπ).symm.toRingHom
  (RingHom.Finite.of_surjective _ (principalAwayFractionEquiv R p hπ).symm.surjective)

private def principalSupportExact := PrincipalComparison.supportExact
  (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (principalAwayFractionEquiv R p hπ)

private def closedOrdinaryIso :
    (FGModuleCat.closedRestrictionExact.{u, u} π).toFunctor ≅
    ((principalResidueRestrictionExact R p hπ).comp
      (FGModuleCat.IdealSupport.closedRestrictionExact
        (localPoint R p).asIdeal)).toFunctor := by
  let e := principalClosedResidueEquiv R p hπ
  have he : Ideal.Quotient.mk (Ideal.span {π}) =
      e.symm.toRingHom.comp (Ideal.Quotient.mk (localPoint R p).asIdeal) := by
    ext r
    apply e.injective
    change e (Ideal.Quotient.mk (Ideal.span {π}) r) =
      e (e.symm (Ideal.Quotient.mk (localPoint R p).asIdeal r))
    rw [e.apply_symm_apply]
    exact Ideal.quotEquivOfEq_mk hπ.maximalIdeal_eq.symm r
  let η := ModuleCat.restrictScalarsComp'.{u}
    (Ideal.Quotient.mk (localPoint R p).asIdeal) e.symm.toRingHom
    (Ideal.Quotient.mk (Ideal.span {π})) he
  exact NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (η.app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact η.hom.naturality f.hom)

private def supportClosedIso :
    ((FGModuleCat.Localization.smallClosedToSupportExact π).comp
      (principalSupportExact R p hπ)).toFunctor ≅
    ((principalResidueRestrictionExact R p hπ).smallModel.comp
      (DedekindResidue.quotientResidueSupportExactFunctor (Localization.AtPrime p.asIdeal)
        (localPoint R p))).toFunctor := by
  apply Functor.fullyFaithfulCancelRight
    (FGModuleCat.Localization.supported (nonZeroDivisors (Localization.AtPrime p.asIdeal))).ι
  change (FGModuleCat.closedRestrictionExact.{u, u} π).smallModel.toFunctor ⋙
      (ExactFunctor.id (abelianExactStructure
        (FGModuleCat.{u} (Localization.AtPrime p.asIdeal)))).smallModel.toFunctor ≅ _
  exact Functor.isoWhiskerLeft
      (FGModuleCat.closedRestrictionExact.{u, u} π).smallModel.toFunctor
      (ExactFunctor.smallModelIdIso
        (abelianExactStructure (FGModuleCat.{u} (Localization.AtPrime p.asIdeal)))) ≪≫
    Functor.rightUnitor (FGModuleCat.closedRestrictionExact.{u, u} π).smallModel.toFunctor ≪≫
    ExactFunctor.smallModelNatIso (closedOrdinaryIso R p hπ) ≪≫
    ExactFunctor.smallModelCompIso (principalResidueRestrictionExact R p hπ)
      (FGModuleCat.IdealSupport.closedRestrictionExact
        (localPoint R p).asIdeal) ≪≫
    Functor.isoWhiskerLeft (principalResidueRestrictionExact R p hπ).smallModel.toFunctor
      (quotientResidueSupportInclusionIso (Localization.AtPrime p.asIdeal)
        (localPoint R p)).symm


set_option maxHeartbeats 4000000 in
-- Unfolding the original supported functor square crosses several native small-model comparisons.
private theorem supportClosedKMap (n : ℕ) :
    ((principalSupportExact R p hπ).KMap n).comp
      (FGModuleCat.Localization.closedSupportGEquiv.{u, u} π n).toMonoidHom =
    (localResidueSupportKEquiv R p n).toMonoidHom.comp
      ((principalResidueRestrictionExact R p hπ).smallKMap.{u} n) := by
  have h := ExactFunctor.KMap_eq_of_natIso (supportClosedIso R p hπ) n
  have hleft := ExactFunctor.KMap_comp
    (FGModuleCat.Localization.smallClosedToSupportExact.{u, u} π)
    (principalSupportExact R p hπ) n
  have hright := ExactFunctor.KMap_comp
    (principalResidueRestrictionExact R p hπ).smallModel
    (DedekindResidue.quotientResidueSupportExactFunctor
      (Localization.AtPrime p.asIdeal) (localPoint R p)) n
  have hcomp := hleft.symm.trans (h.trans hright)
  apply MonoidHom.ext
  intro a
  have hl := DFunLike.congr_fun (FGModuleCat.Localization.closedSupportGEquiv_coe π n) a
  change FGModuleCat.Localization.closedSupportGEquiv.{u, u} π n a =
    (FGModuleCat.Localization.smallClosedToSupportExact π).KMap n a at hl
  change (principalSupportExact R p hπ).KMap n
      (FGModuleCat.Localization.closedSupportGEquiv.{u, u} π n a) =
    localResidueSupportKEquiv R p n ((principalResidueRestrictionExact R p hπ).smallKMap.{u} n a)
  exact (congrArg ((principalSupportExact R p hπ).KMap n) hl).trans
    ((DFunLike.congr_fun hcomp a).trans
      (localResidueSupportKEquiv_apply R p n
        ((principalResidueRestrictionExact R p hπ).smallKMap.{u} n a)).symm)

set_option maxHeartbeats 4000000 in
-- The exact original boundary square retains its explicit supported-functor normalizations.
/-- The original native principal-closed boundary agrees with the original local-DVR boundary
after the prescribed scalar restrictions, in every degree. -/
theorem principalBoundary_nativeBoundary (n : ℕ) :
    ((principalResidueRestrictionExact R p hπ).smallKMap.{u} n).comp
      (FGModuleCat.Localization.closedConnectingHom.{u, u} π n) =
    (localDvrBoundary R p n).comp
      ((principalFractionRestrictionExact R p hπ).smallKMap.{u} (n + 1)) := by
  apply MonoidHom.ext
  intro a
  apply (localResidueSupportKEquiv R p n).injective
  have hs := DFunLike.congr_fun (supportClosedKMap R p hπ n)
    (FGModuleCat.Localization.closedConnectingHom.{u, u} π n a)
  have hclosed : FGModuleCat.Localization.closedSupportGEquiv.{u, u} π n
      (FGModuleCat.Localization.closedConnectingHom.{u, u} π n a) =
    FGModuleCat.Localization.connectingHom (Submonoid.powers π) n a :=
    (FGModuleCat.Localization.closedSupportGEquiv.{u, u} π n).apply_symm_apply _
  have hn := DFunLike.congr_fun
    (PrincipalComparison.connectingHom_square
      (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
      (principalAwayFractionEquiv R p hπ) n) a
  have hlocal : localResidueSupportKEquiv R p n
      (localDvrBoundary R p n
        ((principalFractionRestrictionExact R p hπ).smallKMap.{u} (n + 1) a)) =
    FGModuleCat.Localization.connectingHom (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n
      ((principalFractionRestrictionExact R p hπ).smallKMap.{u} (n + 1) a) :=
    (localResidueSupportKEquiv R p n).apply_symm_apply _
  exact hs.symm.trans
    ((congrArg ((principalSupportExact R p hπ).KMap n) hclosed).trans (hn.trans hlocal.symm))

end FGModuleCat.DedekindLocalDvr
