/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ClopenModelFactor
public import Colib.AlgebraicGeometry.Divisors.SectionKernelOpenRestriction

/-! # Actual marked-component factors of original sections

A section from a connected base lands in the marked normal component of the
curve. The base need not be local. Connectedness is essential: one marked point
cannot control sections over other connected components of the base. The final
inclusion is only a clopen immersion; no Cartesian whole-curve square over the
identity of the base is asserted. Uncompiled candidate.
-/
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme
variable {A C : Scheme.{u}} [PreconnectedSpace A]
  [IsLocallyNoetherian C] [IsNormal C]

/-- The actual image of a map from a preconnected base remains in the marked
clopen component, not just its value at the marking. -/
theorem range_subset_normalComponent_of_mark
    (σ : A ⟶ C) (a : A) (x : C) (hx : σ a ∈ normalComponentOpen x) :
    Set.range σ ⊆ Set.range (normalComponentOpen x).ι := by
  rw [Opens.range_ι]
  exact (isPreconnected_range σ.continuous).subset_isClopen
    (isClopen_normalComponentOpen x) ⟨σ a, ⟨a, rfl⟩, hx⟩

/-- The original map factored through the actual marked normal component. -/
def markedNormalComponentFactor
    (σ : A ⟶ C) (a : A) (x : C) (hx : σ a ∈ normalComponentOpen x) :
    A ⟶ (normalComponentOpen x).toScheme :=
  IsOpenImmersion.lift (normalComponentOpen x).ι σ
    (range_subset_normalComponent_of_mark σ a x hx)

@[simp, reassoc] theorem markedNormalComponentFactor_ι
    (σ : A ⟶ C) (a : A) (x : C) (hx : σ a ∈ normalComponentOpen x) :
    markedNormalComponentFactor σ a x hx ≫ (normalComponentOpen x).ι = σ :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both original sections land in exactly the component through their common
marked value. Their full kernels are the original kernels restricted along the
actual clopen inclusion, with no whole-curve Cartesian assumption. -/
theorem exists_markedNormalComponent_section_pair
    (q : C ⟶ A) (σ τ : A ⟶ C)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    (hσ : σ ≫ q = 𝟙 A) (hτ : τ ≫ q = 𝟙 A)
    (a : A) (hst : σ a = τ a) :
    ∃ (σ' τ' : A ⟶ (normalComponentOpen (σ a)).toScheme),
      σ' ≫ (normalComponentOpen (σ a)).ι = σ ∧
      τ' ≫ (normalComponentOpen (σ a)).ι = τ ∧
      σ' ≫ ((normalComponentOpen (σ a)).ι ≫ q) = 𝟙 A ∧
      τ' ≫ ((normalComponentOpen (σ a)).ι ≫ q) = 𝟙 A ∧
      σ'.ker = σ.ker.comap (normalComponentOpen (σ a)).ι ∧
      τ'.ker = τ.ker.comap (normalComponentOpen (σ a)).ι := by
  have hs : σ a ∈ normalComponentOpen (σ a) := mem_normalComponentOpen _
  have ht : τ a ∈ normalComponentOpen (σ a) := by rw [← hst]; exact hs
  let σ' := markedNormalComponentFactor σ a (σ a) hs
  let τ' := markedNormalComponentFactor τ a (σ a) ht
  have hσ' : σ' ≫ (normalComponentOpen (σ a)).ι = σ :=
    markedNormalComponentFactor_ι σ a (σ a) hs
  have hτ' : τ' ≫ (normalComponentOpen (σ a)).ι = τ :=
    markedNormalComponentFactor_ι τ a (σ a) ht
  refine ⟨σ', τ', hσ', hτ', ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hσ', hσ]
  · rw [← Category.assoc, hτ', hτ]
  · exact ker_section_openRestriction _ σ σ' hσ'
  · exact ker_section_openRestriction _ τ τ' hτ'

end AlgebraicGeometry.Scheme
