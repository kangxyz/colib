/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.AssociatedUnitGluing
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.BoundaryUnit

/-!
# Gluing association units with prescribed boundary values

Chartwise association of the determinant norm and the target coefficient
gives a global quotient on the chosen open. The two full boundary maps
factor through that open and read one.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

/-- Association units glue with their actual values on both boundary maps. -/
theorem exists_normQuotientOnBoundaries_of_association_cover
    {X Y B₁ B₂ : Scheme.{u}} (U : Y.Opens)
    (g : X ⟶ U.toScheme) [Stacks.Morphisms.IsFiniteLocallyFree g]
    (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y)
    (h₁ : Set.range m₁ ⊆ (U : Set Y)) (h₂ : Set.range m₂ ⊆ (U : Set Y))
    {I : Type v} (V : I → U.toScheme.Opens) (hcover : (⊤ : U.toScheme.Opens) ≤ iSup V)
    (cB : Γ(X, ⊤)) (cA : Γ(U.toScheme, ⊤))
    (μ : ∀ i, Γ((V i).toScheme, ⊤)ˣ)
    (hreg : ∀ i j, IsRightRegular ((V i ⊓ V j : U.toScheme.Opens).ι.appTop cA))
    (hNorm : ∀ i, (V i).ι.appTop (normTop g cB) =
      (μ i : Γ((V i).toScheme, ⊤)) * (V i).ι.appTop cA)
    (hval₁ : ∀ i, (pullback.snd m₁ ((V i).ι ≫ U.ι)).appTop
      (μ i : Γ((V i).toScheme, ⊤)) = 1)
    (hval₂ : ∀ i, (pullback.snd m₂ ((V i).ι ≫ U.ι)).appTop
      (μ i : Γ((V i).toScheme, ⊤)) = 1) :
    NormQuotientOnBoundaries U g m₁ m₂ cB cA := by
  obtain ⟨u, hu, hChart⟩ :=
    exists_associationUnit_of_appTop_cover V hcover cA (normTop g cB) μ hreg hNorm
  let lift {D : Scheme.{u}} (m : D ⟶ Y) (hm : Set.range m ⊆ (U : Set Y)) :=
    IsOpenImmersion.lift U.ι m (by simpa only [Opens.range_ι] using hm)
  have hLift {D : Scheme.{u}} (m : D ⟶ Y) (hm : Set.range m ⊆ (U : Set Y)) :
      lift m hm ≫ U.ι = m := IsOpenImmersion.lift_fac _ _ _
  let v (i : I) := (V i).ι ≫ U.ι
  have hone {D : Scheme.{u}} (m : D ⟶ Y) (hm : Set.range m ⊆ (U : Set Y))
      (hval : ∀ i, (pullback.snd m (v i)).appTop (μ i : Γ((V i).toScheme, ⊤)) = 1) :
      (lift m hm).appTop (u : Γ(U.toScheme, ⊤)) = 1 := by
    apply appTop_eq_one_of_compatible_cover (lift m hm) V
      (fun i ↦ pullback.fst m (v i)) (fun i ↦ pullback.snd m (v i))
    · intro i
      apply (cancel_mono U.ι).mp
      calc
        _ = pullback.fst m (v i) ≫ lift m hm ≫ U.ι := Category.assoc _ _ _
        _ = pullback.fst m (v i) ≫ m := congrArg (fun w ↦ pullback.fst m (v i) ≫ w) (hLift m hm)
        _ = pullback.snd m (v i) ≫ v i := pullback.condition
        _ = _ := (Category.assoc _ _ _).symm
    · intro x
      let y := lift m hm x
      obtain ⟨i, hiy⟩ := Opens.mem_iSup.mp (hcover (show y ∈ (⊤ : U.toScheme.Opens) from trivial))
      have hx : m x = v i ⟨y, hiy⟩ := congrArg (fun k ↦ k x) (hLift m hm).symm
      obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback m (v i)) x ⟨y, hiy⟩ hx
      exact ⟨i, a, ha⟩
    · intro i
      exact (congrArg (fun a ↦ (pullback.snd m (v i)).appTop a) (hChart i)).trans (hval i)
  let l := coprod.desc (lift m₁ h₁) (lift m₂ h₂)
  have hl : l ≫ U.ι = coprod.desc m₁ m₂ := by
    apply coprod.hom_ext
    · simp only [l, coprod.inl_desc_assoc, coprod.inl_desc, hLift]
    · simp only [l, coprod.inr_desc_assoc, coprod.inr_desc, hLift]
  have hlOne : l.appTop (u : Γ(U.toScheme, ⊤)) = 1 := by
    apply globalSections_coprod_ext
    · rw [← CommRingCat.comp_apply, ← Hom.comp_appTop]
      simpa only [l, coprod.inl_desc, map_one] using hone m₁ h₁ hval₁
    · rw [← CommRingCat.comp_apply, ← Hom.comp_appTop]
      simpa only [l, coprod.inr_desc, map_one] using hone m₂ h₂ hval₂
  let r := U.topIso.hom ((u⁻¹ : Γ(U.toScheme, ⊤)ˣ) : Γ(U.toScheme, ⊤))
  refine ⟨r, l, (u⁻¹).isUnit.map U.topIso.hom.hom, hl, ?_, ?_⟩
  · dsimp only [r]
    rw [Iso.hom_inv_id_apply]
    have hUnit : Units.map l.appTop.hom.toMonoidHom u = 1 := Units.ext hlOne
    have hInv : Units.map l.appTop.hom.toMonoidHom u⁻¹ = 1 := by
      rw [map_inv, hUnit, inv_one]
    exact congrArg (fun v : Γ(B₁ ⨿ B₂, ⊤)ˣ ↦ (v : Γ(B₁ ⨿ B₂, ⊤))) hInv
  · dsimp only [r]
    rw [Iso.hom_inv_id_apply, hu, mul_right_comm]
    simp

/-- Association on an affine subopen, including the two actual boundary restrictions. -/
abbrev NormAssociationOnRestriction
    {C Y B₁ B₂ : Scheme.{u}} (F : C ⟶ Y) (U : Y.Opens)
    (hF : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd F U.ι))
    (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y)
    (cB : Γ((pullback F U.ι : Scheme.{u}), ⊤)) (cA : Γ(U.toScheme, ⊤))
    (V : U.toScheme.Opens) : Prop :=
  ∃ μ : Γ(V.toScheme, ⊤)ˣ,
    V.ι.appTop ((@normTop _ _ (pullback.snd F U.ι) hF) cB) =
      (μ : Γ(V.toScheme, ⊤)) * V.ι.appTop cA ∧
    (pullback.snd m₁ (V.ι ≫ U.ι)).appTop (μ : Γ(V.toScheme, ⊤)) = 1 ∧
    (pullback.snd m₂ (V.ι ≫ U.ι)).appTop (μ : Γ(V.toScheme, ⊤)) = 1

/-- Freeness of the actual algebra of a chart of a finite morphism. -/
abbrev IsFreeNormChart {C Y W : Scheme.{u}} (F : C ⟶ Y) (w : W ⟶ Y) : Prop :=
  letI : Algebra Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) :=
    (pullback.snd F w).appTop.hom.toAlgebra
  Module.Free Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤)

/-- Association on each free affine norm chart gives the normalized unit on
the whole open. -/
theorem exists_normQuotientOnBoundaries_of_affine_association
    {C Y B₁ B₂ : Scheme.{u}} (F : C ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree F]
    (U : Y.Opens) [IsSeparated (terminal.from U.toScheme)]
    (hF : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd F U.ι))
    (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y)
    (h₁ : Set.range m₁ ⊆ (U : Set Y)) (h₂ : Set.range m₂ ⊆ (U : Set Y))
    (cB : Γ((pullback F U.ι : Scheme.{u}), ⊤)) (cA : Γ(U.toScheme, ⊤))
    (hChart : ∀ (V : U.toScheme.Opens), IsAffineOpen V →
      IsFreeNormChart F (V.ι ≫ U.ι) →
      NormAssociationOnRestriction F U hF m₁ m₂ cB cA V)
    (hreg : ∀ (V : U.toScheme.Opens), IsAffineOpen V → IsRightRegular (V.ι.appTop cA)) :
    @NormQuotientOnBoundaries _ _ _ _ U (pullback.snd F U.ι) hF m₁ m₂ cB cA := by
  let : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd F U.ι) := hF
  choose V hV hxV hFree using exists_freeAffineNormChart F U
  have hAssoc (x : U.toScheme) := hChart (V x) (hV x) (hFree x)
  choose μ hNorm hLeft hRight using hAssoc
  exact exists_normQuotientOnBoundaries_of_association_cover U (pullback.snd F U.ι) m₁ m₂
    h₁ h₂ V (fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxV x⟩) cB cA μ
    (fun i j ↦ hreg _ ((hV i).inf (hV j))) hNorm hLeft hRight

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
