/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.PrincipalBoundaryComparison
public import Colib.AlgebraicGeometry.KTheory.CoherentPrincipalBoundaryComparison
public import Colib.AlgebraicGeometry.KTheory.CoherentAffineRingIso

/-!
# Literal principal scheme boundaries and the original local-DVR boundary

The original geometric principal boundary, after its prescribed fraction and
residue isomorphism pullbacks, equals the original native local-DVR boundary.
The final theorem retains an arbitrary supplied fraction field and its algebra
structure. It uses actual scalar restriction along the canonical inverse
field transport, not an unspecified group isomorphism or a choice of sign.

Implementation source: `Quillen/GTheory/Dedekind/PrincipalDvrBoundaryComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, the two original scheme consumers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped nonZeroDivisors

namespace FGModuleCat.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
variable {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)

private def principalFractionReverseExact :=
  FGModuleCat.finiteRestrictionExact.{u, u, u}
  (principalAwayFractionEquiv R p hπ).toRingHom
  (RingHom.Finite.of_surjective _ (principalAwayFractionEquiv R p hπ).surjective)

private def openRoundTripIso :
    ((principalFractionReverseExact R p hπ).comp
      (principalFractionRestrictionExact R p hπ)).toFunctor ≅
    (ExactFunctor.id (abelianExactStructure (FGModuleCat.{u}
      (FractionRing (Localization.AtPrime p.asIdeal))))).toFunctor := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (principalAwayFractionEquiv R p hπ).toRingEquiv
  exact NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (E.unitIso.symm.app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact E.unitIso.inv.naturality f.hom)

private theorem openRoundTripKMap (n : ℕ) :
    ((principalFractionRestrictionExact R p hπ).smallKMap n).comp
      ((principalFractionReverseExact R p hπ).smallKMap n) =
      MonoidHom.id _ := by
  have h := ExactFunctor.smallKMap_eq_of_natIso (openRoundTripIso R p hπ) n
  simpa only [ExactFunctor.smallKMap_comp, ExactFunctor.smallKMap_id] using h

/-- The literal principal-closed scheme boundary, with its original generic and closed
isomorphism pullbacks, agrees with the native local-DVR boundary in every degree. -/
theorem principalSchemeBoundary_nativeBoundary (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of (FractionRing (Localization.AtPrime p.asIdeal)))) (n + 1)) :
    publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n
          (Scheme.pullbackG
            (Spec.map (principalAwayFractionEquiv R p hπ).toRingEquiv.symm.toCommRingCatIso.hom)
            (n + 1) a))) =
    localDvrBoundary R p n
      (publicSpecGRingEquiv (CommRingCat.of (FractionRing (Localization.AtPrime p.asIdeal)))
        (n + 1) a) := by
  let z := Scheme.pullbackG
    (Spec.map (principalAwayFractionEquiv R p hπ).toRingEquiv.symm.toCommRingCatIso.hom) (n + 1) a
  have hc := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback (principalClosedResidueEquiv R p hπ) n)
      (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n z)
  have hp := DFunLike.congr_fun
    (publicSpecGRingEquiv_principalClosed_boundaryG
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n) z
  have hn := DFunLike.congr_fun (principalBoundary_nativeBoundary R p hπ n)
    (publicSpecGRingEquiv (CommRingCat.of (Localization.Away π)) (n + 1) z)
  have ho := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback
      (principalAwayFractionEquiv R p hπ).toRingEquiv.symm (n + 1)) a
  have hr := DFunLike.congr_fun (openRoundTripKMap R p hπ (n + 1))
    (publicSpecGRingEquiv
      (CommRingCat.of (FractionRing (Localization.AtPrime p.asIdeal))) (n + 1) a)
  exact hc.trans ((congrArg ((principalResidueRestrictionExact R p hπ).smallKMap n) hp).trans
    (hn.trans (congrArg (localDvrBoundary R p n)
      ((congrArg ((principalFractionRestrictionExact R p hπ).smallKMap (n + 1)) ho).trans hr))))
end FGModuleCat.DedekindLocalDvr


namespace FGModuleCat.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local instance : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _
variable (K : Type u) [Field K] [Algebra (Localization.AtPrime p.asIdeal) K]
  [IsFractionRing (Localization.AtPrime p.asIdeal) K]
variable {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)
include hπ

/-- The supplied fraction field is the actual localization away from the chosen irreducible. -/
theorem principalField_isLocalizationAway : IsLocalization.Away π K := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := K)
    (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
  · infer_instance
  · intro a ha
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp ha) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

/-- The canonical principal-open equivalence to the supplied actual fraction field. -/
def principalAwayFieldEquiv : Localization.Away π ≃ₐ[Localization.AtPrime p.asIdeal] K :=
  letI := principalField_isLocalizationAway R p K hπ
  IsLocalization.algEquiv (Submonoid.powers π) _ _

omit hπ in
/-- The canonical algebra equivalence from the native fraction ring to the supplied field. -/
def localFractionFieldEquiv :
    FractionRing (Localization.AtPrime p.asIdeal) ≃ₐ[Localization.AtPrime p.asIdeal] K :=
  IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime p.asIdeal)) _ _

private theorem inverseAlgEquiv :
    (principalAwayFieldEquiv R p K hπ).symm =
      (localFractionFieldEquiv R p K).symm.trans (principalAwayFractionEquiv R p hπ).symm := by
  ext x
  have h : (principalAwayFieldEquiv R p K hπ).symm.toAlgHom =
      ((localFractionFieldEquiv R p K).symm.trans
        (principalAwayFractionEquiv R p hπ).symm).toAlgHom :=
    (IsLocalization.algHom_subsingleton (nonZeroDivisors (Localization.AtPrime p.asIdeal))).elim _ _
  exact DFunLike.congr_fun h x

private theorem inverseSpecTriangle :
    Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom =
      Spec.map (principalAwayFractionEquiv R p hπ).symm.toRingEquiv.toCommRingCatIso.hom ≫
        Spec.map (localFractionFieldEquiv R p K).symm.toRingEquiv.toCommRingCatIso.hom := by
  change Spec.map (CommRingCat.ofHom (principalAwayFieldEquiv R p K hπ).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (principalAwayFractionEquiv R p hπ).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (localFractionFieldEquiv R p K).symm.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : K →+* Localization.Away π => Spec.map (CommRingCat.ofHom f))
    (congrArg (fun e : K ≃ₐ[Localization.AtPrime p.asIdeal] Localization.Away π =>
      e.toRingHom) (inverseAlgEquiv R p K hπ))

omit hπ in
private theorem pullbackG_congr {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {f g : X ⟶ Y}
    [Flat f] [Flat g] (h : f = g) (n : ℕ) : Scheme.pullbackG f n = Scheme.pullbackG g n := by
  subst g
  rfl

/-- The literal principal boundary with the supplied actual fraction field agrees with
the original native local-DVR boundary after canonical inverse field transport, in every degree. -/
theorem principalSchemeBoundary_nativeBoundary_field (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of K)) (n + 1)) :
    publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n
          (Scheme.pullbackG
            (Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom)
            (n + 1) a))) =
    localDvrBoundary R p n
      ((FGModuleCat.finiteRestrictionExact.{u, u, u}
        (localFractionFieldEquiv R p K).toRingHom
        (RingHom.Finite.of_surjective _ (localFractionFieldEquiv R p K).surjective)).smallKMap
          (n + 1)
          (publicSpecGRingEquiv (CommRingCat.of K) (n + 1) a)) := by
  have hg : Scheme.pullbackG
      (Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom) (n + 1) =
    (Scheme.pullbackG
      (Spec.map (principalAwayFractionEquiv R p hπ).symm.toRingEquiv.toCommRingCatIso.hom)
      (n + 1)).comp
        (Scheme.pullbackG
          (Spec.map (localFractionFieldEquiv R p K).symm.toRingEquiv.toCommRingCatIso.hom)
          (n + 1)) := by
    exact (pullbackG_congr (inverseSpecTriangle R p K hπ) (n + 1)).trans
      (Scheme.pullbackG_comp _ _ (n + 1))
  have hz := DFunLike.congr_fun hg a
  have hf := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback
      (localFractionFieldEquiv R p K).symm.toRingEquiv (n + 1)) a
  exact (congrArg (fun z => publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n z))) hz).trans
    ((principalSchemeBoundary_nativeBoundary R p hπ n
      (Scheme.pullbackG
        (Spec.map (localFractionFieldEquiv R p K).symm.toRingEquiv.toCommRingCatIso.hom)
        (n + 1) a)).trans (congrArg (localDvrBoundary R p n) hf))
end FGModuleCat.DedekindLocalDvr

attribute [colib_tag "COL-0613",
  colib_ref "quillen" "Quillen/GTheory/Dedekind/PrincipalDvrBoundaryComparison.lean"
    "adaptation" "Original principal geometric boundary with native and supplied fraction fields"]
  FGModuleCat.DedekindLocalDvr.principalSchemeBoundary_nativeBoundary
  FGModuleCat.DedekindLocalDvr.principalSchemeBoundary_nativeBoundary_field
