/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedBoundarySections

/-!
# Actual scalar-normalized sections on the entire boundary

The second signed correction uses two sections of one ample power with a
prescribed scalar ratio. The scalar is an actual unit automorphism of the full
boundary structure module, constructed componentwise by boundary gluing in the
application. Coherent Serre restriction produces both sections; their whole zero
schemes on the retained curve are finite and relative Cartier.

Adapted from `RelativeCurve/Sections/DivisorPairs/NormalizedScalar.lean` and
`AffineSource.lean` at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance (Y : Scheme.{u}) (M : Y.Modules) [hM : IsInvertibleModule Y M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M :=
  hM

variable {X S Z : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  (i : Z ⟶ X) [IsClosedImmersion i]
  (E : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf)

include f hL in
/-- Coherent Serre restriction constructs the actual scalar-normalized pair,
with both entire boundary zero schemes empty. -/
theorem exists_eventually_scalar_boundary_sections :
    let c : Γ(Z, ⊤) := Modules.Hom.app (X := Z) E.hom ⊤ (1 : Γ(Z, ⊤))
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ _eT : (Modules.pullback i).obj (tensorPowModule X L (n : ℤ)) ≅
        SheafOfModules.unit Z.ringCatSheaf,
      ∃ s t : Γ(tensorPowModule X L (n : ℤ), ⊤),
        pullbackGlobalSections i _ s =
          c • pullbackGlobalSections i _ t ∧
        zeroScheme Z ((Modules.pullback i).obj (tensorPowModule X L (n : ℤ)))
          (pullbackGlobalSections i _ s) = ⊤ ∧
        zeroScheme Z ((Modules.pullback i).obj (tensorPowModule X L (n : ℤ)))
          (pullbackGlobalSections i _ t) = ⊤ := by
  obtain ⟨N, hN⟩ := exists_eventually_surjective_boundary_restriction f L hL i
  refine ⟨N, fun n hn eT => ?_⟩
  let T := tensorPowModule X L (n : ℤ)
  let c : Γ(Z, ⊤) := Modules.Hom.app (X := Z) E.hom ⊤ (1 : Γ(Z, ⊤))
  obtain ⟨s, hs⟩ := hN n hn ((eT ≪≫ E.symm).inv.app ⊤ (1 : Γ(Z, ⊤)))
  obtain ⟨t, ht⟩ := hN n hn (eT.inv.app ⊤ (1 : Γ(Z, ⊤)))
  refine ⟨s, t, ?_, ?_, ?_⟩
  · have h : (eT ≪≫ E.symm).inv.app ⊤ (1 : Γ(Z, ⊤)) =
        c • eT.inv.app ⊤ (1 : Γ(Z, ⊤)) := by
      change eT.inv.app ⊤ c = c • eT.inv.app ⊤ (1 : Γ(Z, ⊤))
      exact (congrArg (fun r : Γ(Z, ⊤) => eT.inv.app ⊤ r) (mul_one c).symm).trans
        (Modules.Hom.app_smul eT.inv c (1 : Γ(Z, ⊤)))
    exact hs.trans (h.trans (congrArg (fun t => c • t) ht.symm))
  · exact (congrArg (fun a => zeroScheme Z ((Modules.pullback i).obj T) a) hs).trans
      (zeroScheme_inverse_frame _ (eT ≪≫ E.symm))
  · exact (congrArg (fun a => zeroScheme Z ((Modules.pullback i).obj T) a) ht).trans
      (zeroScheme_inverse_frame _ eT)

include hL in
/-- Both scalar-prescribed divisors are genuinely finite flat on the unchanged
retained curve. No regularity or finite-flatness premise is supplied. -/
theorem exists_eventually_scalar_boundary_divisors {C : Scheme.{u}}
    (j : C ⟶ X) [IsOpenImmersion j] [C.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ f)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    let c : Γ(Z, ⊤) := Modules.Hom.app (X := Z) E.hom ⊤ (1 : Γ(Z, ⊤))
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ _eT : (Modules.pullback i).obj (tensorPowModule X L (n : ℤ)) ≅
        SheafOfModules.unit Z.ringCatSheaf,
      ∃ s t : Γ(tensorPowModule X L (n : ℤ), ⊤),
        pullbackGlobalSections i _ s =
          c • pullbackGlobalSections i _ t ∧
        IsIso (sectionUnitHom _ (pullbackGlobalSections i _ s)) ∧
        IsIso (sectionUnitHom _ (pullbackGlobalSections i _ t)) ∧
        (IsFinite ((zeroScheme C ((Modules.pullback j).obj (tensorPowModule X L (n : ℤ)))
            (pullbackGlobalSections j _ s)).subschemeι ≫ (j ≫ f)) ∧
          Stacks.Divisors.IsRelativeEffectiveCartierDivisor (j ≫ f)
            (zeroScheme C ((Modules.pullback j).obj (tensorPowModule X L (n : ℤ)))
              (pullbackGlobalSections j _ s))) ∧
        (IsFinite ((zeroScheme C ((Modules.pullback j).obj (tensorPowModule X L (n : ℤ)))
            (pullbackGlobalSections j _ t)).subschemeι ≫ (j ≫ f)) ∧
          Stacks.Divisors.IsRelativeEffectiveCartierDivisor (j ≫ f)
            (zeroScheme C ((Modules.pullback j).obj (tensorPowModule X L (n : ℤ)))
              (pullbackGlobalSections j _ t))) := by
  obtain ⟨N, hN⟩ := exists_eventually_scalar_boundary_sections f L hL i E
  refine ⟨N, fun n hn eT => ?_⟩
  obtain ⟨s, t, hst, hs, ht⟩ := hN n hn eT
  exact ⟨s, t, hst, isIso_sectionUnitHom_of_zeroScheme_eq_top _ _ hs,
    isIso_sectionUnitHom_of_zeroScheme_eq_top _ _ ht,
    finite_relativeCartier_of_boundary_zero i f j hcover _ s hs,
    finite_relativeCartier_of_boundary_zero i f j hcover _ t ht⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
