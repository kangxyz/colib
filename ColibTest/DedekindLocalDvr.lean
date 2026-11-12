/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.LocalDvrBoundaryNaturality

/-! # Original-map consumers of native Dedekind local-DVR coordinates -/

@[expose] public section
noncomputable section
universe u
open FGModuleCat FGModuleCat.DedekindLocalDvr
open scoped nonZeroDivisors DirectSum
namespace ColibTest.DedekindLocalDvr
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The original tensor map, not an unspecified fraction-field group isomorphism,
is retained in every prescribed local-DVR coordinate. -/
theorem finiteFamilyWithOriginalTensorMap
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 1))
    (a : ⨁ p, Additive (DedekindResidue.ResidueFieldK R p 1)) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (FractionRing R) 2,
      Additive.ofMul (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) 1 b) =
        DedekindResidue.residueFieldAssemblyKEquiv R 0 a ∧
      ∀ p, localDvrBoundary R p 1
        ((FGModuleCat.finiteModuleExtensionExact (fractionRingMap R p)).smallKMap 2 b) =
          (a p).toMul :=
  localDvrG1_finite_family_lift R h a

/-- Original local-DVR coordinates detect precisely the actual generic G₂ image. -/
theorem genericGTwoImage :
    (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 2).range =
      ⨅ p, (localDvrBoundaryFromGlobal R p 1).ker :=
  genericG2_range_eq_iInf_localDvrBoundaryK1_ker R

end ColibTest.DedekindLocalDvr
