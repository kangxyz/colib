/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange

/-! # Transport the same finite-stage marks to the original geometric field

E is not assumed algebraically closed. Apply with the original E → L → Ω map,
where Ω is the algebraically closed field required by the restriction consumer.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart

/-- Base extension of the field of a mark preserves every chart equation by
composition; the chart, section and good-tail lift are unchanged. -/
theorem fieldMark_transport
    {E Ω : Type u} [Field E] [Field Ω] (φ : E →+* Ω)
    {A Y Z V U D : Scheme.{u}}
    (q : A ⟶ Z) (s : Y ⟶ Z) (k : V ⟶ Y)
    (ξ : Spec (.of E) ⟶ A) (η : Spec (.of E) ⟶ Y)
    (ηV : Spec (.of E) ⟶ V) (hξ : ξ ≫ q = η ≫ s) (hη : ηV ≫ k = η)
    (i : A ⟶ U) (xE : Spec (.of E) ⟶ U) (hx : ξ ≫ i = xE)
    (e : D ⟶ U) (ζ : Spec (.of E) ⟶ D) (hζ : ζ ≫ e = xE) :
    let β := Spec.map (CommRingCat.ofHom φ)
    (β ≫ ξ) ≫ q = (β ≫ η) ≫ s ∧
    (β ≫ ηV) ≫ k = β ≫ η ∧
    (β ≫ ξ) ≫ i = β ≫ xE ∧
    (β ≫ ζ) ≫ e = β ≫ xE := by
  let β := Spec.map (CommRingCat.ofHom φ)
  exact ⟨(Category.assoc _ _ _).trans
      ((congrArg (fun z => β ≫ z) hξ).trans (Category.assoc _ _ _).symm),
    (Category.assoc _ _ _).trans (congrArg (fun z => β ≫ z) hη),
    (Category.assoc _ _ _).trans (congrArg (fun z => β ≫ z) hx),
    (Category.assoc _ _ _).trans (congrArg (fun z => β ≫ z) hζ)⟩

/-- The already-constructed good-tail chart mark is preserved on its actual
pullback, not merely on its underlying point. -/
theorem fieldMark_baseChange_chart
    {E Ω : Type u} [Field E] [Field Ω] (φ : E →+* Ω)
    {A Y Z V : Scheme.{u}} (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)
    (hs : s ≫ p = 𝟙 Y) (k : V ⟶ Y)
    (ξ : Spec (.of E) ⟶ A) (η : Spec (.of E) ⟶ Y)
    (hξ : ξ ≫ q = η ≫ s) (ηV : Spec (.of E) ⟶ V) (hη : ηV ≫ k = η) :
    let β := Spec.map (CommRingCat.ofHom φ)
    β ≫ MarkedBaseChange.chartMark q p s hs k ξ η hξ ηV hη ≫
      CategoryTheory.Limits.pullback.snd k (q ≫ p) = β ≫ ξ :=
  congrArg (fun z => Spec.map (CommRingCat.ofHom φ) ≫ z)
    (MarkedBaseChange.chartMark_original q p s hs k ξ η hξ ηV hη)

/-- The original geometric target equation composes with finite-stage recovery. -/
theorem fieldMark_original_target
    {E Ω : Type u} [Field E] [Field Ω] (φ : E →+* Ω)
    {A U T : Scheme.{u}} (ξ : Spec (.of E) ⟶ A) (i : A ⟶ U)
    (xE : Spec (.of E) ⟶ U) (hx : ξ ≫ i = xE) (t : U ⟶ T)
    (xΩ : Spec (.of Ω) ⟶ T)
    (hOriginal : Spec.map (CommRingCat.ofHom φ) ≫ xE ≫ t = xΩ) :
    (Spec.map (CommRingCat.ofHom φ) ≫ ξ) ≫ (i ≫ t) = xΩ := by
  calc
    _ = Spec.map (CommRingCat.ofHom φ) ≫ (ξ ≫ (i ≫ t)) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom φ) ≫ ((ξ ≫ i) ≫ t) :=
      congrArg (fun z => Spec.map (CommRingCat.ofHom φ) ≫ z) (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom φ) ≫ (xE ≫ t) :=
      congrArg (fun z => Spec.map (CommRingCat.ofHom φ) ≫ (z ≫ t)) hx
    _ = xΩ := hOriginal

end AlgebraicGeometry.Scheme.EtaleChart
