/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer

/-!
# Whole-source Serre lifting on the native sheaf tensor product

The eventual section-surjectivity theorem is proved from the pinned relative Serre theorem,
not supplied as a vanishing or lifting hypothesis. The source scheme and the quotient map
are unchanged. In particular, a later boundary application must identify its actual closed
boundary quotient with this map; no dense-open restriction is part of this construction.

Implementation provenance: the section-existence step of
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Data/Serre.lean`, blob
`a291270368be1902e271bc9cf1b5a91780200938`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The proof is rewritten using the pinned Stacks tensor, cohomology and ample-module APIs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Ample Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

include f hL

/-- Native relative Serre vanishing makes the whole-source section map of a twisted
short exact sequence surjective. Only its actual kernel must be coherent. -/
theorem exists_eventually_surjective_twisted_sections
    (C : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)) (hC : C.ShortExact)
    (hK : C.X₁.IsCoherent) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((twistFunctor L (n : ℤ)).map C.g)).hom := by
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.absoluteVanishingOverAffineBase
      X S f inferInstance inferInstance inferInstance L hL C.X₁ hK 1 (by decide)
  refine ⟨N, fun n hn => ?_⟩
  let := isInvertibleModule_tensorPowModule X L (n : ℤ)
  have hCn : (C.map (twistFunctor L (n : ℤ))).ShortExact :=
    Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight X
      (tensorPowModule X L (n : ℤ)) hC
  apply Stacks.AmpleCohomologicalCriterion.surjective_evaluation_map_g X ⊤ hCn
  exact (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    X.ringCatSheaf ⊤ 1 _).mpr (hN n hn)

/-- Every sufficiently high twist of the actual coherent quotient map lifts all its
whole-source sections. There is no supplied section or cohomology-vanishing premise. -/
theorem exists_eventually_surjective_twisted_quotient
    {M Q : X.Modules} [M.IsCoherent] [Q.IsCoherent] (π : M ⟶ Q) [Epi π] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((twistFunctor L (n : ℤ)).map π)).hom :=
  exists_eventually_surjective_twisted_sections f L hL (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := inferInstance }
    (AlgebraicGeometry.CoherentAbelian.isCoherent_kernel π)

/-- One common Serre bound lifts two independently prescribed whole-boundary values.
The values are arbitrary sections of the actual twisted quotients, not chosen lifts. -/
theorem exists_eventually_prescribed_twisted_pair
    {M₁ Q₁ M₂ Q₂ : X.Modules}
    [M₁.IsCoherent] [Q₁.IsCoherent] [M₂.IsCoherent] [Q₂.IsCoherent]
    (π₁ : M₁ ⟶ Q₁) [Epi π₁] (π₂ : M₂ ⟶ Q₂) [Epi π₂] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ q₁ : Γ((twistFunctor L (n : ℤ)).obj Q₁, ⊤),
      ∀ q₂ : Γ((twistFunctor L (n : ℤ)).obj Q₂, ⊤),
      ∃ s₁ : Γ((twistFunctor L (n : ℤ)).obj M₁, ⊤),
      ∃ s₂ : Γ((twistFunctor L (n : ℤ)).obj M₂, ⊤),
        Modules.Hom.app ((twistFunctor L (n : ℤ)).map π₁) ⊤ s₁ = q₁ ∧
        Modules.Hom.app ((twistFunctor L (n : ℤ)).map π₂) ⊤ s₂ = q₂ := by
  obtain ⟨N₁, h₁⟩ := exists_eventually_surjective_twisted_quotient f L hL π₁
  obtain ⟨N₂, h₂⟩ := exists_eventually_surjective_twisted_quotient f L hL π₂
  refine ⟨max N₁ N₂, fun n hn q₁ q₂ => ?_⟩
  obtain ⟨s₁, hs₁⟩ := h₁ n ((le_max_left _ _).trans hn) q₁
  obtain ⟨s₂, hs₂⟩ := h₂ n ((le_max_right _ _).trans hn) q₂
  exact ⟨s₁, s₂, hs₁, hs₂⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
