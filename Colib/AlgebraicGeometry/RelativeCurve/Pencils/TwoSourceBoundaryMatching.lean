/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedMatching

/-!
# Matching for two independent section sources

The first pair and second pair are kept on their own compactified products.
Only their actual pullbacks enter the common pencil. The lower comparison here
is used with the scalar equality produced by CommonBoundaryCoordinates.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {XA XN X ZA ZN Z : Scheme.{u}}
  (gA : X ⟶ XA) (gN : X ⟶ XN) (iA : ZA ⟶ XA) (iN : ZN ⟶ XN) (i : Z ⟶ X)
  (vA : Z ⟶ ZA) (vN : Z ⟶ ZN)
  (hA : i ≫ gA = vA ≫ iA) (hN : i ≫ gN = vN ≫ iN)

/-- Two separate normalizations give matching of the actual pulled product
sections. Neither section pair is replaced by sections on the common source. -/
theorem boundary_tensor_matching_two_sources (F T : XA.Modules) (N : XN.Modules)
    (eF : (Modules.pullback iA).obj F ≅ SheafOfModules.unit ZA.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤)) (n d : Γ(N, ⊤))
    (c : Γ(ZN, ⊤))
    (ha : (fixedFactorBoundaryIso iA F T eF).hom.app ⊤
      (pullbackGlobalSections iA _ a) = pullbackGlobalSections iA _ b)
    (hn : pullbackGlobalSections iN N n = c • pullbackGlobalSections iN N d)
    (hc : vA.appTop (eF.hom.app ⊤ (pullbackGlobalSections iA F σ)) = vN.appTop c) :
    pullbackGlobalSections i _
      (tensorSection ((Modules.pullback gA).obj (tensorModules F T))
        ((Modules.pullback gN).obj N) ⊤
          (pullbackGlobalSections gA _ a) (pullbackGlobalSections gN N n)) =
      pullbackGlobalSections i _
        (tensorSection ((Modules.pullback gA).obj (tensorModules F T))
          ((Modules.pullback gN).obj N) ⊤
            (pullbackGlobalSections gA _ (tensorSection F T ⊤ σ b))
            (pullbackGlobalSections gN N d)) := by
  apply boundary_tensor_matching_after_sourceChange gA iA i vA hA F T
    ((Modules.pullback gN).obj N) eF σ a b _ _ ha
  rw [hc]
  exact boundary_smul_identity_after_sourceChange gN iN i vN hN N n d c hn

/-- The empty whole-boundary zero scheme of a section survives either actual
source-change square. -/
theorem zeroScheme_boundary_after_sourceChange {X X' Z Z' : Scheme.{u}}
    (g : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (β : Z' ⟶ Z)
    (h : i' ≫ g = β ≫ i) (M : X.Modules) [IsInvertibleModule X M]
    (a : Γ(M, ⊤))
    (ha : zeroScheme Z ((Modules.pullback i).obj M) (pullbackGlobalSections i M a) = ⊤) :
    zeroScheme Z' ((Modules.pullback i').obj ((Modules.pullback g).obj M))
      (pullbackGlobalSections i' _ (pullbackGlobalSections g M a)) = ⊤ := by
  rw [zeroScheme_pullback, zeroScheme_pullback, ← IdealSheafData.comap_comp, h,
    IdealSheafData.comap_comp, ← zeroScheme_pullback i M a, ha,
    IdealSheafData.comap_top]

/-- Nonvanishing of both factors on the complete boundary makes their literal
tensor product nonvanishing there. -/
theorem zeroScheme_boundary_tensorSection_eq_top {X Z : Scheme.{u}} (i : Z ⟶ X)
    (M N : X.Modules) [IsInvertibleModule X M] [IsInvertibleModule X N]
    (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (ha : zeroScheme Z ((Modules.pullback i).obj M) (pullbackGlobalSections i M a) = ⊤)
    (hb : zeroScheme Z ((Modules.pullback i).obj N) (pullbackGlobalSections i N b) = ⊤) :
    zeroScheme Z ((Modules.pullback i).obj (tensorModules M N))
      (pullbackGlobalSections i _ (tensorSection M N ⊤ a b)) = ⊤ := by
  rw [← zeroScheme_congr_iso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i M N),
    pullbackTensorIso_tensorSection, zeroScheme_tensorSection_eq_mul, ha, hb, top_mul]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
