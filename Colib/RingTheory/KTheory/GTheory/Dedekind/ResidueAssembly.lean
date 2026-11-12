/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.PrimarySupport
public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueDevissage

/-!
# Original-map quotient-residue assembly for Dedekind torsion support

In every positive degree, the direct sum of the native finite-module G-groups
of the actual quotient rings `R / p` is equivalent to the original native
torsion-support K-group. The forward map on a singleton is the original
quotient restriction to primary modules followed by the original primary
inclusion. Composing with the supported-to-ambient map gives the sum of the
original quotient restriction maps into `G R`.

The source uses quotient rings. Its comparison with separately presented
residue fields is a distinct step. No finiteness assumption on residue fields
is needed, and no degree-zero direct-sum comparison is asserted here.

## Implementation provenance

Adapted from `Quillen/GTheory/Dedekind/ResidueAssembly.lean` at Quillen commit
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
open FGModuleCat.IdealSupport
open scoped nonZeroDivisors DirectSum ZeroObject

namespace FGModuleCat.DedekindResidue

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The actual quotient-residue finite-module G-group in its native small model. -/
abbrev QuotientResidueK (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :=
  FGModuleCat.FractionLocalization.G.{u, u} (ResidueQuotient R p) n

/-- The actual residue pushforward into native torsion support, at matching small endpoints. -/
def quotientResidueSupportExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactFunctor
      (abelianExactStructure (FGModuleCat.{u} (ResidueQuotient R p))).smallModel
      (abelianExactStructure (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors
        R)).FullSubcategory) :=
  (residueToPrimaryExact R p).comp (nativePrimaryInclusionExactFunctor R p)

/-- The original normalized K-map of the residue pushforward into support. -/
def quotientResidueSupportKMap (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    QuotientResidueK R p n →*
      FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n :=
  (quotientResidueSupportExactFunctor R p).KMap n

/-- The original residue pushforward factors through the original primary inclusion. -/
theorem quotientResidueSupportKMap_eq (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    quotientResidueSupportKMap R p n =
      ((nativePrimaryInclusionExactFunctor R p).KMap n).comp
        ((residueToPrimaryExact R p).KMap n) :=
  ExactFunctor.KMap_comp _ _ n

/-- The direct sum of the proved residue-to-primary dévissage equivalences. -/
def residuePrimaryDirectSumEquiv (n : ℕ) :
    (⨁ p, Additive (QuotientResidueK R p (n + 1))) ≃+
      ⨁ p, Additive (DedekindPrimary.PrimaryK R p (n + 1)) :=
  DFinsupp.mapRange.addEquiv (fun p => (residuePrimaryKEquiv R p (n + 1)).toAdditive)

/-- Each direct-sum coordinate retains the original quotient restriction equivalence. -/
@[simp]
theorem residuePrimaryDirectSumEquiv_of (n : ℕ)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (a : Additive (QuotientResidueK R p (n + 1))) :
    residuePrimaryDirectSumEquiv R n (DirectSum.of _ p a) =
      DirectSum.of (fun q => Additive (DedekindPrimary.PrimaryK R q (n + 1))) p
        (Additive.ofMul (residuePrimaryKEquiv R p (n + 1) a.toMul)) := by
  change DirectSum.map
    (fun p => (residuePrimaryKEquiv R p (n + 1)).toAdditive.toAddMonoidHom)
      (DirectSum.of _ p a) = _
  exact DirectSum.map_of
    (fun q => (residuePrimaryKEquiv R q (n + 1)).toAdditive.toAddMonoidHom) p a

/-- Positive-degree quotient-residue assembly into the original native torsion support. -/
def quotientResidueAssemblyKEquiv (n : ℕ) :
    (⨁ p, Additive (QuotientResidueK R p (n + 1))) ≃+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1)) :=
  (residuePrimaryDirectSumEquiv R n).trans (DedekindPrimary.primaryAssemblyKEquiv R n)

/-- On each singleton, assembly is the original residue restriction and primary inclusion. -/
@[simp]
theorem quotientResidueAssemblyKEquiv_of (n : ℕ)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (a : Additive (QuotientResidueK R p (n + 1))) :
    quotientResidueAssemblyKEquiv R n (DirectSum.of _ p a) =
      Additive.ofMul ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1)
        ((residueToPrimaryExact R p).KMap (n + 1) a.toMul)) := by
  change DedekindPrimary.primaryAssemblyKEquiv R n
    (residuePrimaryDirectSumEquiv R n (DirectSum.of _ p a)) = _
  rw [residuePrimaryDirectSumEquiv_of, DedekindPrimary.primaryAssemblyKEquiv_of]
  exact congrArg
    (fun x => Additive.ofMul ((nativePrimaryInclusionExactFunctor R p).KMap (n + 1) x))
    (DFunLike.congr_fun (residuePrimaryKEquiv_toMonoidHom R p (n + 1)) a.toMul)

/-- The sum of the original residue pushforward K-maps into native support. -/
def quotientResidueAssemblyKMap (n : ℕ) :
    (⨁ p, Additive (QuotientResidueK R p (n + 1))) →+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1)) :=
  DirectSum.toAddMonoid (fun p => (quotientResidueSupportKMap R p (n + 1)).toAdditive)

/-- The forward assembly equivalence is exactly the sum of the original residue pushforwards. -/
theorem quotientResidueAssemblyKEquiv_toAddMonoidHom (n : ℕ) :
    ((quotientResidueAssemblyKEquiv R n).toAddMonoidHom :
      (⨁ p, Additive (QuotientResidueK R p (n + 1))) →+
        Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1))) =
      quotientResidueAssemblyKMap R n := by
  apply DirectSum.addHom_ext
  intro p a
  change quotientResidueAssemblyKEquiv R n (DirectSum.of _ p a) =
    quotientResidueAssemblyKMap R n (DirectSum.of _ p a)
  rw [quotientResidueAssemblyKEquiv_of, quotientResidueAssemblyKMap, DirectSum.toAddMonoid_of]
  exact congrArg Additive.ofMul
    (DFunLike.congr_fun (quotientResidueSupportKMap_eq R p (n + 1)) a.toMul).symm

/-- The original residue assembly is the finite sum over the actual support of an element. -/
theorem quotientResidueAssemblyKEquiv_eq_sum (n : ℕ)
    (a : ⨁ p, Additive (QuotientResidueK R p (n + 1))) :
    quotientResidueAssemblyKEquiv R n a = ∑ p ∈ a.support,
      Additive.ofMul (quotientResidueSupportKMap R p (n + 1) (a p).toMul) := by
  calc
    quotientResidueAssemblyKEquiv R n a = quotientResidueAssemblyKMap R n a :=
      DFunLike.congr_fun (quotientResidueAssemblyKEquiv_toAddMonoidHom R n) a
    _ = quotientResidueAssemblyKMap R n
        (∑ p ∈ a.support,
          DirectSum.of (fun q => Additive (QuotientResidueK R q (n + 1))) p (a p)) :=
      congrArg (quotientResidueAssemblyKMap R n) (DirectSum.sum_support_of a).symm
    _ = _ := by
      change (DirectSum.toAddMonoid
        (fun p => (quotientResidueSupportKMap R p (n + 1)).toAdditive))
        (∑ p ∈ a.support,
          DirectSum.of (fun q => Additive (QuotientResidueK R q (n + 1))) p (a p)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact DirectSum.toAddMonoid_of
        (fun p => (quotientResidueSupportKMap R p (n + 1)).toAdditive) p (a p)

/-- The supported-to-ambient map retains the original quotient restriction pushforward. -/
theorem supportedKMap_comp_quotientResidueSupport
    (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    (FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) n).comp
        (quotientResidueSupportKMap R p n) =
      (closedRestrictionExact p.asIdeal).smallKMap n := by
  rw [quotientResidueSupportKMap_eq, ← MonoidHom.comp_assoc,
    DedekindPrimary.supportedKMap_comp_primaryInclusion]
  calc
    (DedekindPrimary.primaryAmbientKMap R p n).comp
        ((residueToPrimaryExact R p).KMap n) =
      (DedekindPrimary.primaryAmbientKMap R p n).comp
        (residuePrimaryKEquiv R p n).toMonoidHom :=
      congrArg ((DedekindPrimary.primaryAmbientKMap R p n).comp)
        (residuePrimaryKEquiv_toMonoidHom R p n).symm
    _ = _ := residuePrimaryKEquiv_comp_ambient R p n

/-- Sum of the original quotient restrictions into actual finite-module G-theory. -/
def quotientResidueAmbientAssemblyKMap (n : ℕ) :
    (⨁ p, Additive (QuotientResidueK R p (n + 1))) →+
      Additive (FGModuleCat.FractionLocalization.G.{u, u} R (n + 1)) :=
  DirectSum.toAddMonoid (fun p => ((closedRestrictionExact p.asIdeal).smallKMap (n + 1)).toAdditive)

set_option maxHeartbeats 800000 in
-- The native supported inclusion unfolds the small-model localization comparison.
/-- The original supported-to-ambient map composed with assembly is the sum of pushforwards. -/
theorem supportedKMap_comp_quotientResidueAssembly (n : ℕ) :
    ((FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) (n + 1)).toAdditive).comp
        ((quotientResidueAssemblyKEquiv R n).toAddMonoidHom :
          (⨁ p, Additive (QuotientResidueK R p (n + 1))) →+
            Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1))) =
      quotientResidueAmbientAssemblyKMap R n := by
  apply DirectSum.addHom_ext
  intro p a
  change Additive.ofMul (FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) (n + 1)
    (quotientResidueAssemblyKEquiv R n (DirectSum.of _ p a)).toMul) =
      quotientResidueAmbientAssemblyKMap R n (DirectSum.of _ p a)
  rw [quotientResidueAssemblyKEquiv_of, quotientResidueAmbientAssemblyKMap,
    DirectSum.toAddMonoid_of]
  have h := DFunLike.congr_fun (supportedKMap_comp_quotientResidueSupport R p (n + 1)) a.toMul
  rw [quotientResidueSupportKMap_eq] at h
  exact congrArg Additive.ofMul h

/-- Quotient-residue assembly in degree one, with its original pushforward maps. -/
abbrev quotientResidueK1AssemblyEquiv :
    (⨁ p, Additive (QuotientResidueK R p 1)) ≃+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) 1) :=
  quotientResidueAssemblyKEquiv R 0

/-- Quotient-residue assembly in degree two, with its original pushforward maps. -/
abbrev quotientResidueK2AssemblyEquiv :
    (⨁ p, Additive (QuotientResidueK R p 2)) ≃+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) 2) :=
  quotientResidueAssemblyKEquiv R 1

end FGModuleCat.DedekindResidue
