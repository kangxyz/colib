/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueField
public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueAssembly

/-!
# Native residue-field assembly for Dedekind torsion support

In every positive degree, the direct sum of the native finite-module G-groups
of `Ideal.ResidueField` is equivalent to the original native torsion-support
K-group. The comparison first uses the canonical quotient-to-residue-field
algebra equivalence, then the proved quotient-residue assembly. Its singleton
maps are the original exact pushforwards into support. Composing with the
supported-to-ambient map gives the sum of the original scalar restrictions
along R into its residue fields, with their original zero normalizations.

The actual source and support models both use the native common universe `u`.
No finiteness assumption on residue fields is needed. This is the module
endpoint of residue assembly; no identification with scheme residue fields
and no degree-zero direct-sum equivalence are asserted.

## Implementation provenance

Adapted from `Quillen/GTheory/Dedekind/ResidueFieldAssembly.lean` at Quillen commit
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
open scoped nonZeroDivisors DirectSum ZeroObject

namespace FGModuleCat.DedekindResidue

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- Actual finite-module G-theory of the native `Ideal.ResidueField`. -/
abbrev ResidueFieldK (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :=
  FGModuleCat.FractionLocalization.G.{u, u} p.asIdeal.ResidueField n

/-- Original residue-field restriction followed by the original pushforward into support. -/
def residueFieldSupportExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactFunctor
      (abelianExactStructure (FGModuleCat.{u} p.asIdeal.ResidueField)).smallModel
      (abelianExactStructure (FGModuleCat.Localization.supported.{u, u} (nonZeroDivisors
        R)).FullSubcategory) :=
  (residueFieldRestrictionExact R p).smallModel.comp (quotientResidueSupportExactFunctor R p)

/-- The original normalized K-map of the exact residue-field pushforward into support. -/
def residueFieldSupportKMap (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    ResidueFieldK R p n →* FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n :=
  (residueFieldSupportExactFunctor R p).KMap n

/-- The original pushforward factors through the canonical quotient comparison. -/
theorem residueFieldSupportKMap_eq (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    residueFieldSupportKMap R p n =
      (quotientResidueSupportKMap R p n).comp (residueFieldKEquiv R p n).toMonoidHom :=
  ExactFunctor.KMap_comp _ _ n

/-- The direct sum of the canonical native residue-field-to-quotient K-equivalences. -/
def residueFieldDirectSumEquiv (n : ℕ) :
    (⨁ p, Additive (ResidueFieldK R p (n + 1))) ≃+
      ⨁ p, Additive (QuotientResidueK R p (n + 1)) :=
  DFinsupp.mapRange.addEquiv (fun p => (residueFieldKEquiv R p (n + 1)).toAdditive)

/-- Each singleton retains the original canonical scalar-restriction K-map. -/
@[simp] theorem residueFieldDirectSumEquiv_of (n : ℕ)
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : Additive (ResidueFieldK R p (n + 1))) :
    residueFieldDirectSumEquiv R n (DirectSum.of _ p a) =
      DirectSum.of (fun q => Additive (QuotientResidueK R q (n + 1))) p
        (Additive.ofMul (residueFieldKEquiv R p (n + 1) a.toMul)) := by
  change DirectSum.map
    (fun p => (residueFieldKEquiv R p (n + 1)).toAdditive.toAddMonoidHom)
      (DirectSum.of _ p a) = _
  exact DirectSum.map_of
    (fun q => (residueFieldKEquiv R q (n + 1)).toAdditive.toAddMonoidHom) p a

/-- Positive-degree native residue-field assembly into the actual torsion support. -/
def residueFieldAssemblyKEquiv (n : ℕ) :
    (⨁ p, Additive (ResidueFieldK R p (n + 1))) ≃+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1)) :=
  (residueFieldDirectSumEquiv R n).trans (quotientResidueAssemblyKEquiv R n)

/-- A singleton assembles by its original exact residue-field pushforward. -/
@[simp] theorem residueFieldAssemblyKEquiv_of (n : ℕ)
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : Additive (ResidueFieldK R p (n + 1))) :
    residueFieldAssemblyKEquiv R n (DirectSum.of _ p a) =
      Additive.ofMul (residueFieldSupportKMap R p (n + 1) a.toMul) := by
  change quotientResidueAssemblyKEquiv R n
    (residueFieldDirectSumEquiv R n (DirectSum.of _ p a)) = _
  rw [residueFieldDirectSumEquiv_of, quotientResidueAssemblyKEquiv_of]
  apply congrArg Additive.ofMul
  change ((FGModuleCat.PrimaryDecomposition.nativePrimaryInclusionExactFunctor
      R p).KMap (n + 1))
      ((residueToPrimaryExact R p).KMap (n + 1)
        (residueFieldKEquiv R p (n + 1) a.toMul)) = _
  rw [residueFieldSupportKMap_eq, quotientResidueSupportKMap_eq]
  rfl

/-- The sum of the original residue-field pushforwards into native support. -/
def residueFieldAssemblyKMap (n : ℕ) :
    (⨁ p, Additive (ResidueFieldK R p (n + 1))) →+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1)) :=
  DirectSum.toAddMonoid (fun p => (residueFieldSupportKMap R p (n + 1)).toAdditive)

/-- The assembly equivalence has exactly the sum of original pushforwards as forward map. -/
@[simp] theorem residueFieldAssemblyKEquiv_toAddMonoidHom (n : ℕ) :
    ((residueFieldAssemblyKEquiv R n).toAddMonoidHom :
      (⨁ p, Additive (ResidueFieldK R p (n + 1))) →+
        Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1))) =
      residueFieldAssemblyKMap R n := by
  apply DirectSum.addHom_ext
  intro p a
  change residueFieldAssemblyKEquiv R n (DirectSum.of _ p a) =
    residueFieldAssemblyKMap R n (DirectSum.of _ p a)
  rw [residueFieldAssemblyKEquiv_of, residueFieldAssemblyKMap, DirectSum.toAddMonoid_of]
  rfl

/-- Assembly is the finite sum over the actual support of the given family. -/
theorem residueFieldAssemblyKEquiv_eq_sum (n : ℕ)
    (a : ⨁ p, Additive (ResidueFieldK R p (n + 1))) :
    residueFieldAssemblyKEquiv R n a = ∑ p ∈ a.support,
      Additive.ofMul (residueFieldSupportKMap R p (n + 1) (a p).toMul) := by
  calc
    residueFieldAssemblyKEquiv R n a = residueFieldAssemblyKMap R n a :=
      DFunLike.congr_fun (residueFieldAssemblyKEquiv_toAddMonoidHom R n) a
    _ = residueFieldAssemblyKMap R n
        (∑ p ∈ a.support,
          DirectSum.of (fun q => Additive (ResidueFieldK R q (n + 1))) p (a p)) :=
      congrArg (residueFieldAssemblyKMap R n) (DirectSum.sum_support_of a).symm
    _ = _ := by
      change (DirectSum.toAddMonoid
        (fun p => (residueFieldSupportKMap R p (n + 1)).toAdditive))
        (∑ p ∈ a.support,
          DirectSum.of (fun q => Additive (ResidueFieldK R q (n + 1))) p (a p)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact DirectSum.toAddMonoid_of
        (fun p => (residueFieldSupportKMap R p (n + 1)).toAdditive) p (a p)

/-- The support inclusion retains the original restriction along the R-map into the field. -/
theorem supportedKMap_comp_residueFieldSupport
    (p : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) :
    (FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) n).comp
        (residueFieldSupportKMap R p n) =
      (residueFieldPushforwardExact R p).smallKMap n := by
  rw [residueFieldSupportKMap_eq, ← MonoidHom.comp_assoc,
    supportedKMap_comp_quotientResidueSupport]
  exact residueFieldKEquiv_comp_pushforward R p n

/-- Sum of the original residue-field scalar restrictions into finite-module G-theory of R. -/
def residueFieldAmbientAssemblyKMap (n : ℕ) :
    (⨁ p, Additive (ResidueFieldK R p (n + 1))) →+
      Additive (FGModuleCat.FractionLocalization.G.{u, u} R (n + 1)) :=
  DirectSum.toAddMonoid
    (fun p => ((residueFieldPushforwardExact R p).smallKMap (n + 1)).toAdditive)

set_option maxHeartbeats 800000 in
-- The native supported inclusion unfolds the small-model localization comparison.
/-- Assembly followed by the original support inclusion is the sum of original pushforwards. -/
theorem supportedKMap_comp_residueFieldAssembly (n : ℕ) :
    ((FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) (n + 1)).toAdditive).comp
        ((residueFieldAssemblyKEquiv R n).toAddMonoidHom :
          (⨁ p, Additive (ResidueFieldK R p (n + 1))) →+
            Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) (n + 1))) =
      residueFieldAmbientAssemblyKMap R n := by
  apply DirectSum.addHom_ext
  intro p a
  change Additive.ofMul (FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) (n + 1)
    (residueFieldAssemblyKEquiv R n (DirectSum.of _ p a)).toMul) =
      residueFieldAmbientAssemblyKMap R n (DirectSum.of _ p a)
  rw [residueFieldAssemblyKEquiv_of, residueFieldAmbientAssemblyKMap,
    DirectSum.toAddMonoid_of]
  exact congrArg Additive.ofMul
    (DFunLike.congr_fun (supportedKMap_comp_residueFieldSupport R p (n + 1)) a.toMul)

/-- The original supported-to-ambient map is the explicit finite sum of scalar restrictions. -/
theorem supportedKMap_residueFieldAssembly_eq_sum (n : ℕ)
    (a : ⨁ p, Additive (ResidueFieldK R p (n + 1))) :
    Additive.ofMul (FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) (n + 1)
      (residueFieldAssemblyKEquiv R n a).toMul) =
      ∑ p ∈ a.support,
        Additive.ofMul ((residueFieldPushforwardExact R p).smallKMap (n + 1)
          (a p).toMul) := by
  change ((FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) (n + 1)).toAdditive)
    (residueFieldAssemblyKEquiv R n a) = _
  rw [residueFieldAssemblyKEquiv_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact congrArg Additive.ofMul
    (DFunLike.congr_fun (supportedKMap_comp_residueFieldSupport R p (n + 1)) (a p).toMul)

/-- Native residue-field assembly in degree one, with the original pushforward maps. -/
abbrev residueFieldK1AssemblyEquiv :
    (⨁ p, Additive (ResidueFieldK R p 1)) ≃+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) 1) :=
  residueFieldAssemblyKEquiv R 0

/-- Native residue-field assembly in degree two, with the original pushforward maps. -/
abbrev residueFieldK2AssemblyEquiv :
    (⨁ p, Additive (ResidueFieldK R p 2)) ≃+
      Additive (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) 2) :=
  residueFieldAssemblyKEquiv R 1

attribute [colib_tag "COL-0603",
  colib_ref "WeibelKBook" "V, Sections 6.6–6.7.3" "comparison"
    "Dedekind localization context; the named original maps specify the implementation",
  colib_ref "quillen" "Quillen/GTheory/Dedekind/ResidueFieldAssembly.lean" "adaptation"
    "Canonical positive-degree residue assembly and its original supported-to-ambient maps"]
  residueFieldAssemblyKEquiv residueFieldAssemblyKEquiv_of
  residueFieldAssemblyKEquiv_eq_sum supportedKMap_comp_residueFieldAssembly
  supportedKMap_residueFieldAssembly_eq_sum

end FGModuleCat.DedekindResidue
