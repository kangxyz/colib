/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FixedFactorRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundarySupport

/-!
# Actual normalized numerator and denominator from fixed-factor Serre restriction

The fixed factor is an invertible native module, not a second ample line. Its
specified whole-boundary frame and a coefficient-power frame determine the two
values to lift. Serre restriction produces the global sections. The normalization
is stated using the actual pullback tensor comparison, the fixed-factor frame and
the native left unitor. Thus no matching equation, section, vanishing hypothesis,
regular divisor or finite-flat zero scheme is an input.

The tensor order is `F tensor T`. The original
`RelativeCurve/Sections/DivisorPairs/AffineSource.lean` uses `T tensor F`;
its equation is the braiding of this literal comparison. No second line-bundle
model is introduced. Source: `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Ample Stacks.SheafOfModules.Invertible Stacks.Divisors
open Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- Remove the fixed factor on the boundary using its prescribed frame.
Every map in this comparison is the native pullback or tensor map. -/
def fixedFactorBoundaryIso (F T : X.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback i).obj ((Stacks.AffineClosedUnion.twistFunctor X T).obj F) ≅
      (Modules.pullback i).obj T :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i F T ≪≫
    tensorProductIso _ _ eF (Iso.refl _) ≪≫ tensorProductLeftUnitor _ _ _

/-- Reading the inverse of the tensor frame through the fixed-factor comparison
recovers exactly the inverse coefficient frame. -/
theorem fixedFactorBoundaryIso_inverse_frame (F T : X.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eT : (Modules.pullback i).obj T ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (fixedFactorBoundaryIso i F T eF).hom.app ⊤
        ((fixedFactorBoundaryIso i F T eF ≪≫ eT).inv.app ⊤ 1) =
      eT.inv.app ⊤ 1 := by
  change (fixedFactorBoundaryIso i F T eF).hom.app ⊤
      ((fixedFactorBoundaryIso i F T eF).inv.app ⊤ (eT.inv.app ⊤ 1)) = _
  exact congrArg (fun m => m.app ⊤ (eT.inv.app ⊤ (1 : Γ(Z, ⊤))))
    (fixedFactorBoundaryIso i F T eF).inv_hom_id

/-- The inverse image of one under an actual frame has unit zero ideal. -/
theorem zeroScheme_inverse_frame (M : Z.Modules) [IsInvertibleModule Z M]
    (e : M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    zeroScheme Z M (e.inv.app ⊤ 1) = ⊤ := by
  apply zeroScheme_eq_top_of_unit_evaluation M _ e.hom
  exact congrArg (fun m => m.app ⊤ (1 : Γ(Z, ⊤))) e.inv_hom_id

variable {S : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  [IsClosedImmersion i] (F : X.Modules) [IsInvertibleModule X F]
  (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- Actual global normalized sections, with empty whole-boundary zeros.
The eventual bound is chosen before the coefficient frame at each power. -/
theorem exists_eventually_normalized_boundary_sections :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ eT : (Modules.pullback i).obj (tensorPowModule X L (n : ℤ)) ≅
        SheafOfModules.unit Z.ringCatSheaf,
      ∃ s : Γ((twistFunctor L (n : ℤ)).obj F, ⊤),
      ∃ t : Γ(tensorPowModule X L (n : ℤ), ⊤),
        (fixedFactorBoundaryIso i F (tensorPowModule X L (n : ℤ)) eF).hom.app ⊤
            (pullbackGlobalSections i _ s) = pullbackGlobalSections i _ t ∧
        zeroScheme Z ((Modules.pullback i).obj ((twistFunctor L (n : ℤ)).obj F))
          (pullbackGlobalSections i _ s) = ⊤ ∧
        zeroScheme Z ((Modules.pullback i).obj (tensorPowModule X L (n : ℤ)))
          (pullbackGlobalSections i _ t) = ⊤ := by
  obtain ⟨N, hN⟩ := exists_eventually_fixedFactor_boundary_pair f L hL i F
  refine ⟨N, fun n hn eT => ?_⟩
  let T := tensorPowModule X L (n : ℤ)
  let eA := fixedFactorBoundaryIso i F T eF ≪≫ eT
  obtain ⟨s, t, hs, ht⟩ := hN n hn (eA.inv.app ⊤ 1) (eT.inv.app ⊤ 1)
  refine ⟨s, t, ?_, ?_, ?_⟩
  · rw [hs, ht]
    exact fixedFactorBoundaryIso_inverse_frame i F T eF eT
  · rw [hs]
    exact zeroScheme_inverse_frame _ eA
  · rw [ht]
    exact zeroScheme_inverse_frame _ eT

/-- The actual whole zero scheme on the retained curve is finite flat once its
restriction to the entire boundary is empty. Compactification smoothness is not
assumed. This helper records the actual zero ideal and source map. -/
theorem finite_relativeCartier_of_boundary_zero {C : Scheme.{u}}
    (j : C ⟶ X) [IsOpenImmersion j] [C.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ f)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤))
    (hs : zeroScheme Z ((Modules.pullback i).obj M)
      (pullbackGlobalSections i M s) = ⊤) :
    IsFinite ((zeroScheme C ((Modules.pullback j).obj M)
        (pullbackGlobalSections j M s)).subschemeι ≫ (j ≫ f)) ∧
      Stacks.Divisors.IsRelativeEffectiveCartierDivisor (j ≫ f)
        (zeroScheme C ((Modules.pullback j).obj M) (pullbackGlobalSections j M s)) := by
  apply finite_relativeCartier_zeroScheme_on_open_of_proper f j M s
  apply whole_support_subset_of_boundary_comap_top j i _ hcover
  rwa [Stacks.Divisors.zeroScheme_pullback] at hs

/-- The fixed-factor Serre producer gives the normalized pair and both actual
finite-flat divisors on the unchanged retained source. The regularity and finite
flatness conclusions are derived for the entire zero schemes. -/
theorem exists_eventually_normalized_boundary_divisors {C : Scheme.{u}}
    (j : C ⟶ X) [IsOpenImmersion j] [C.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ f)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ eT : (Modules.pullback i).obj (tensorPowModule X L (n : ℤ)) ≅
        SheafOfModules.unit Z.ringCatSheaf,
      ∃ s : Γ((twistFunctor L (n : ℤ)).obj F, ⊤),
      ∃ t : Γ(tensorPowModule X L (n : ℤ), ⊤),
        (fixedFactorBoundaryIso i F (tensorPowModule X L (n : ℤ)) eF).hom.app ⊤
            (pullbackGlobalSections i _ s) = pullbackGlobalSections i _ t ∧
        IsIso (sectionUnitHom _ (pullbackGlobalSections i _ s)) ∧
        IsIso (sectionUnitHom _ (pullbackGlobalSections i _ t)) ∧
        (IsFinite ((zeroScheme C ((Modules.pullback j).obj ((twistFunctor L (n : ℤ)).obj F))
            (pullbackGlobalSections j _ s)).subschemeι ≫ (j ≫ f)) ∧
          Stacks.Divisors.IsRelativeEffectiveCartierDivisor (j ≫ f)
            (zeroScheme C ((Modules.pullback j).obj ((twistFunctor L (n : ℤ)).obj F))
              (pullbackGlobalSections j _ s))) ∧
        (IsFinite ((zeroScheme C ((Modules.pullback j).obj (tensorPowModule X L (n : ℤ)))
            (pullbackGlobalSections j _ t)).subschemeι ≫ (j ≫ f)) ∧
          Stacks.Divisors.IsRelativeEffectiveCartierDivisor (j ≫ f)
            (zeroScheme C ((Modules.pullback j).obj (tensorPowModule X L (n : ℤ)))
              (pullbackGlobalSections j _ t))) := by
  obtain ⟨N, hN⟩ := exists_eventually_normalized_boundary_sections i f L hL F eF
  refine ⟨N, fun n hn eT => ?_⟩
  obtain ⟨s, t, hst, hs, ht⟩ := hN n hn eT
  exact ⟨s, t, hst, isIso_sectionUnitHom_of_zeroScheme_eq_top _ _ hs,
    isIso_sectionUnitHom_of_zeroScheme_eq_top _ _ ht,
    finite_relativeCartier_of_boundary_zero i f j hcover _ s hs,
    finite_relativeCartier_of_boundary_zero i f j hcover _ t ht⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
