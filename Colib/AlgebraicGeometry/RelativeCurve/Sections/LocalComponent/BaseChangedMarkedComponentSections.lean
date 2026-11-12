/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Divisors.SectionKernelBaseChange
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.MarkedNormalComponentSections

/-! # Original marked sections through base refinement and then component restriction

The first map F is the genuine curve base change. The second map kappa is a
clopen component inclusion over the same new base. Only the section squares
for kappa are Cartesian; no Cartesian whole-curve square for kappa is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- The actual base-changed sections retain equality at the original refined mark. -/
theorem baseChangedSection_same_marking
    {X A Anew : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A)
    (σ τ : A ⟶ X) (hσ : σ ≫ q = 𝟙 A) (hτ : τ ≫ q = 𝟙 A)
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Anew)
    (hη : η ≫ g = ξ) (hmark : ξ ≫ σ = ξ ≫ τ) :
    η ≫ baseChangedSection q g σ hσ = η ≫ baseChangedSection q g τ hτ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangedSection_fst]
    simpa only [← Category.assoc, hη] using hmark
  · simp only [Category.assoc, baseChangedSection_snd, Category.comp_id]

/-- Both original sections factor through the component of their common refined
mark. Their kernels retain the literal two successive comaps along F and kappa.
The map identities preserve the entire original morphisms, not just point values. -/
theorem exists_baseChanged_markedNormalComponent_section_pair
    {X A Anew : Scheme.{u}} (q : X ⟶ A) [IsSeparated q] (g : Anew ⟶ A)
    [PreconnectedSpace Anew] [IsLocallyNoetherian (pullback q g)]
    [IsNormal (pullback q g)]
    (σ τ : A ⟶ X) (hσ : σ ≫ q = 𝟙 A) (hτ : τ ≫ q = 𝟙 A)
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Anew)
    (hη : η ≫ g = ξ) (hmark : ξ ≫ σ = ξ ≫ τ) :
    let σnew := baseChangedSection q g σ hσ
    let τnew := baseChangedSection q g τ hτ
    let F := pullback.fst q g
    let qnew := pullback.snd q g
    let a := η (IsLocalRing.closedPoint Ω)
    let V := normalComponentOpen (σnew a)
    let κ := V.ι
    σnew ≫ qnew = 𝟙 Anew ∧ τnew ≫ qnew = 𝟙 Anew ∧
    IsPullback σnew g F σ ∧ IsPullback τnew g F τ ∧
    σnew.ker = σ.ker.comap F ∧ τnew.ker = τ.ker.comap F ∧
    η ≫ σnew = η ≫ τnew ∧
    ∃ (σV τV : Anew ⟶ V.toScheme),
      σV ≫ κ = σnew ∧ τV ≫ κ = τnew ∧
      σV ≫ (κ ≫ qnew) = 𝟙 Anew ∧ τV ≫ (κ ≫ qnew) = 𝟙 Anew ∧
      IsPullback σV (𝟙 Anew) κ σnew ∧ IsPullback τV (𝟙 Anew) κ τnew ∧
      σV.ker = (σ.ker.comap F).comap κ ∧
      τV.ker = (τ.ker.comap F).comap κ ∧
      σV ≫ κ ≫ F = g ≫ σ ∧ τV ≫ κ ≫ F = g ≫ τ ∧
      η ≫ σV = η ≫ τV := by
  intro σnew τnew F qnew a V κ
  have hσnew : σnew ≫ qnew = 𝟙 Anew := baseChangedSection_snd q g σ hσ
  have hτnew : τnew ≫ qnew = 𝟙 Anew := baseChangedSection_snd q g τ hτ
  have hσker : σnew.ker = σ.ker.comap F := ker_baseChangedSection q g σ hσ
  have hτker : τnew.ker = τ.ker.comap F := ker_baseChangedSection q g τ hτ
  have hnewmark : η ≫ σnew = η ≫ τnew :=
    baseChangedSection_same_marking q g σ τ hσ hτ ξ η hη hmark
  have hpoint : σnew a = τnew a :=
    congrArg (fun f => f (IsLocalRing.closedPoint Ω)) hnewmark
  let : IsClosedImmersion (σnew ≫ qnew) := by rw [hσnew]; infer_instance
  let : IsClosedImmersion (τnew ≫ qnew) := by rw [hτnew]; infer_instance
  let : IsClosedImmersion σnew := IsClosedImmersion.of_comp σnew qnew
  let : IsClosedImmersion τnew := IsClosedImmersion.of_comp τnew qnew
  obtain ⟨σV, τV, hσV, hτV, hσVq, hτVq, hσVk, hτVk⟩ :=
    exists_markedNormalComponent_section_pair qnew σnew τnew hσnew hτnew a hpoint
  refine ⟨hσnew, hτnew, isPullback_baseChangedSection q g σ hσ,
    isPullback_baseChangedSection q g τ hτ, hσker, hτker, hnewmark,
    σV, τV, hσV, hτV, hσVq, hτVq,
    isPullback_section_openRestriction κ σnew σV hσV,
    isPullback_section_openRestriction κ τnew τV hτV, ?_, ?_, ?_, ?_, ?_⟩
  · exact hσVk.trans (congrArg (fun D => D.comap κ) hσker)
  · exact hτVk.trans (congrArg (fun D => D.comap κ) hτker)
  · rw [← Category.assoc, hσV]
    exact baseChangedSection_fst q g σ hσ
  · rw [← Category.assoc, hτV]
    exact baseChangedSection_fst q g τ hτ
  · apply (cancel_mono κ).mp
    calc
      (η ≫ σV) ≫ κ = η ≫ σnew :=
        (Category.assoc η σV κ).trans (congrArg (fun f => η ≫ f) hσV)
      _ = η ≫ τnew := hnewmark
      _ = (η ≫ τV) ≫ κ :=
        ((Category.assoc η τV κ).trans (congrArg (fun f => η ≫ f) hτV)).symm

end AlgebraicGeometry.Scheme
