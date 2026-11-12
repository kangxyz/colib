/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.Dominance
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.RelativeCurve
public import Colib.AlgebraicGeometry.Chow.NormalComponents
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite support over one component of the native torus

The projection identifies each torus component with the inverse image of the
corresponding base component. A finite support over a component factors through
that actual open torus. A finite change of the torus coordinate has the same
component image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X P : Scheme.{u}} (f : X ⟶ Spec (.of k))

set_option quotPrecheck false in
local notation "τ" => (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
set_option quotPrecheck false in
local notation "π" => pullback.fst f τ

private theorem range_torusOpenExtension (U : X.Opens) :
    Set.range (pullbackParameterExtensionMap U.ι f τ) = π ⁻¹' (U : Set X) := by
  have h := pullbackParameterExtension_isPullback U.ι f τ
  let e := h.isoPullback
  calc
    _ = Set.range (pullback.fst π U.ι) :=
      range_eq_range_of_surjective _ _ e.hom h.isoPullback_hom_fst
    _ = _ := by rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

private theorem isOpenImmersion_torusOpenExtension (U : X.Opens) :
    IsOpenImmersion (pullbackParameterExtensionMap U.ι f τ) :=
  MorphismProperty.of_isPullback (pullbackParameterExtension_isPullback U.ι f τ).flip
    (inferInstance : IsOpenImmersion U.ι)

/-- A finite support over one torus component is finite and surjective over the
native torus above the corresponding open component of the base. -/
theorem exists_finite_surjective_torus_component [IsLocallyNoetherian X] [IsNormal X]
    (g : P ⟶ pullback f τ) [IsFinite g]
    (hrange : Set.range g ∈ irreducibleComponents (pullback f τ : Scheme)) :
    ∃ (U : X.Opens) (g₀ : P ⟶ pullback (U.ι ≫ f) τ),
      IsFinite g₀ ∧ Surjective g₀ ∧ g₀ ≫ pullbackParameterExtensionMap U.ι f τ = g := by
  let : GeometricallyIrreducible τ := inferInstanceAs (GeometricallyIrreducible
    (Scheme.SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  let : Smooth τ := SmoothOfRelativeDimension.smooth 1 τ
  let E := (π).irreducibleComponentsEquiv (π).isOpenMap
  let B := E ⟨Set.range g, hrange⟩
  have hpre : π ⁻¹' (B : Set X) = Set.range g :=
    congrArg Subtype.val (E.symm_apply_apply ⟨Set.range g, hrange⟩)
  let U : X.Opens :=
    ⟨B.val, (isClopen_of_mem_irreducibleComponents_of_isNormal _ B.property).isOpen⟩
  let m := pullbackParameterExtensionMap U.ι f τ
  let : IsOpenImmersion m := isOpenImmersion_torusOpenExtension f U
  have hr : Set.range m = Set.range g := (range_torusOpenExtension f U).trans hpre
  let g₀ := IsOpenImmersion.lift m g hr.ge
  have hg₀ : g₀ ≫ m = g := IsOpenImmersion.lift_fac _ _ _
  let : IsFinite (g₀ ≫ m) := hg₀.symm ▸ inferInstance
  refine ⟨U, g₀, IsFinite.of_comp g₀ m, ⟨fun y => ?_⟩, hg₀⟩
  obtain ⟨x, hx⟩ := hr ▸ (show m y ∈ Set.range m from ⟨y, rfl⟩)
  refine ⟨x, m.isOpenEmbedding.injective ?_⟩
  change (g₀ ≫ m) x = m y
  rwa [hg₀]

/-- A finite change of the torus coordinate has the same irreducible component
image when its projection to the original base is unchanged. -/
theorem range_eq_of_finite_of_torus_component [IsLocallyNoetherian X] [IsNormal X]
    (g h : P ⟶ pullback f τ) [IsFinite g] [IsFinite h]
    (hrange : Set.range g ∈ irreducibleComponents (pullback f τ : Scheme))
    (he : g ≫ π = h ≫ π) : Set.range h = Set.range g := by
  obtain ⟨U, g₀, hgfin, hgsurj, hg⟩ := exists_finite_surjective_torus_component f g hrange
  let m := pullbackParameterExtensionMap U.ι f τ
  let : IsOpenImmersion m := isOpenImmersion_torusOpenExtension f U
  have hm : Set.range g = Set.range m := range_eq_range_of_surjective g m g₀ hg
  have hsub : Set.range h ⊆ Set.range m := by
    rintro _ ⟨x, rfl⟩
    rw [range_torusOpenExtension]
    have hx : g x ∈ Set.range m := hm ▸ ⟨x, rfl⟩
    rw [range_torusOpenExtension] at hx
    change (π) (g x) ∈ (U : Set X) at hx
    change (π) (h x) ∈ (U : Set X)
    have hxeq : (π) (g x) = (π) (h x) := congrArg (fun a => a x) he
    exact hxeq ▸ hx
  let h₀ := IsOpenImmersion.lift m h hsub
  have hh : h₀ ≫ m = h := IsOpenImmersion.lift_fac _ _ _
  let : IsFinite (h₀ ≫ m) := hh.symm ▸ inferInstance
  let : IsFinite h₀ := IsFinite.of_comp h₀ m
  let π₀ := pullback.fst (U.ι ≫ f) τ
  have ht : IsPullback m π₀ π U.ι := pullbackParameterExtension_isPullback U.ι f τ
  have hc (a : P ⟶ pullback (U.ι ≫ f) τ) (b : P ⟶ pullback f τ) (hab : a ≫ m = b) :
      (a ≫ π₀) ≫ U.ι = b ≫ π := by
    rw [Category.assoc, ← ht.w, ← Category.assoc, hab]
  have hp : g₀ ≫ π₀ = h₀ ≫ π₀ := (cancel_mono U.ι).mp
    ((hc g₀ g hg).trans (he.trans (hc h₀ h hh).symm))
  let : Surjective h₀ := surjective_of_finite_of_dominant_torus (U.ι ≫ f) g₀ h₀ hp
  exact (range_eq_range_of_surjective h m h₀ hh).trans hm.symm

end AlgebraicGeometry.NativeTorusPolynomial
