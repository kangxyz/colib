/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.FiniteFlat
public import Colib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.BoundaryFrame

/-!
# Finite flat Cartier zero schemes from a boundary frame

A section with frame coordinate one on the full boundary avoids that boundary
scheme-theoretically. Properness and the quasi-affine smooth curve complement give finiteness
of its whole zero scheme. The smooth-curve criterion then supplies regularity and flatness,
without assuming either. The compactification is not required to be smooth.

All transports use the original zero ideal and its scheme-theoretic inverse image. No reduced
support, integral component selection or assumption on the characteristic of the base enters.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- Cartier regularity can be checked on an open containing the entire closed subscheme. -/
theorem isEffectiveCartierDivisor_of_comap_of_range_subset
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)
    (h : Set.range I.subschemeι ⊆ Set.range j)
    (hI : IsEffectiveCartierDivisor (I.comap j)) : IsEffectiveCartierDivisor I := by
  refine isEffectiveCartierDivisor_of_forall_mem_support I fun x hx => ?_
  obtain ⟨y, rfl⟩ := h (by rwa [Scheme.IdealSheafData.range_subschemeι])
  obtain ⟨V, hV, hyV, a, ha, hideal⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor (I.comap j) hI y
  let e := (j.appIso V).symm.commRingCatIsoToRingEquiv
  refine ⟨⟨j ''ᵁ V, hV.image_of_isOpenImmersion j⟩, e a, ⟨y, hyV, rfl⟩, ?_,
    isRegular_iff_mem_nonZeroDivisors.mp (isRegular_ringEquiv e ha)⟩
  have hmap := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I j ⟨V, hV⟩
  rw [hideal] at hmap
  change Ideal.span {a} = Ideal.comap e.toRingHom _ at hmap
  have hh : Ideal.map e.toRingHom (Ideal.span {a}) =
      I.ideal ⟨j ''ᵁ V, hV.image_of_isOpenImmersion j⟩ :=
    (congrArg (Ideal.map e.toRingHom) hmap).trans
      (Ideal.map_comap_of_surjective _ e.surjective _)
  exact hh.symm.trans (by rw [Ideal.map_span, Set.image_singleton]; rfl)


namespace Scheme.Modules

/-- A finite whole zero scheme supported inside a smooth curve open is Cartier on the
compactification and finite locally free over the base. Its literal restriction has the same
properties. The compactification need not be smooth. -/
@[colib_tag "COL-1046"]
theorem finiteLocallyFree_zeroScheme_on_smooth_open
    {X U S : Scheme.{u}} (q : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) [IsFinite ((zeroScheme X L s).subschemeι ≫ q)]
    (h : Set.range (zeroScheme X L s).subschemeι ⊆ Set.range j) :
    IsRelativeEffectiveCartierDivisor q (zeroScheme X L s) ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X L s).subschemeι ≫ q) ∧
      IsRelativeEffectiveCartierDivisor (j ≫ q) ((zeroScheme X L s).comap j) ∧
      Stacks.Morphisms.IsFiniteLocallyFree (((zeroScheme X L s).comap j).subschemeι ≫ j ≫ q) := by
  let I := zeroScheme X L s
  have : Surjective (pullback.snd j I.subschemeι) := by
    constructor
    intro x
    have hx : x ∈ Set.range (pullback.snd j I.subschemeι) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨x, rfl⟩
    exact hx
  have : IsIso (pullback.snd j I.subschemeι) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  let e : (I.comap j).subscheme ≅ I.subscheme :=
    I.comapIso j ≪≫ asIso (pullback.snd j I.subschemeι)
  have he : e.hom ≫ I.subschemeι = (I.comap j).subschemeι ≫ j := by
    simp only [e, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [← pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hf : (I.comap j).subschemeι ≫ j ≫ q = e.hom ≫ (I.subschemeι ≫ q) := by
    rw [← Category.assoc, ← he, Category.assoc]
  have : IsFinite ((I.comap j).subschemeι ≫ j ≫ q) := by
    rw [hf]
    infer_instance
  have hzero : zeroScheme U ((pullback j).obj L) (pullbackGlobalSections j L s) =
      I.comap j := zeroScheme_pullback j L s
  have : IsFinite ((zeroScheme U ((pullback j).obj L)
      (pullbackGlobalSections j L s)).subschemeι ≫ (j ≫ q)) := by
    rw [hzero]
    infer_instance
  have hcart : IsRelativeEffectiveCartierDivisor (j ≫ q) (I.comap j) := by
    have hc := isRelativeEffectiveCartierDivisor_zeroScheme_of_locallyQuasiFinite
      (j ≫ q) ((pullback j).obj L) (pullbackGlobalSections j L s)
    rwa [hzero] at hc
  obtain ⟨-, -, hflat, hfp⟩ :=
    (isRelativeEffectiveCartierDivisor_iff_locallyQuasiFinite_flat (j ≫ q) _).mp hcart
  have hfree : Stacks.Morphisms.IsFiniteLocallyFree
      ((I.comap j).subschemeι ≫ j ≫ q) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, hflat, hfp⟩
  have hwhole : I.subschemeι ≫ q = e.inv ≫ ((I.comap j).subschemeι ≫ j ≫ q) := by
    rw [hf, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have : Flat (I.subschemeι ≫ q) := by
    rw [hwhole]
    infer_instance
  have : LocallyOfFinitePresentation (I.subschemeι ≫ q) := by
    rw [hwhole]
    infer_instance
  exact ⟨⟨isEffectiveCartierDivisor_of_comap_of_range_subset j I h hcart.1, inferInstance⟩,
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩, hcart, hfree⟩

/-- A literal full-boundary frame equation produces the whole and restricted finite flat
Cartier zero schemes. No regularity, flatness or existence of divisors is an input. -/
@[colib_tag "COL-1046"]
theorem finiteLocallyFree_zeroScheme_of_boundary_frame
    {X B U S : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (q : X ⟶ S) [IsProper q] (i : B ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : Hom.app e.hom ⊤ (pullbackGlobalSections i L s) = (1 : Γ(B, ⊤))) :
    IsRelativeEffectiveCartierDivisor q (zeroScheme X L s) ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X L s).subschemeι ≫ q) ∧
      IsRelativeEffectiveCartierDivisor (j ≫ q) ((zeroScheme X L s).comap j) ∧
      Stacks.Morphisms.IsFiniteLocallyFree (((zeroScheme X L s).comap j).subschemeι ≫ j ≫ q) := by
  have := isFinite_zeroScheme_of_boundary_frame q i j hcover L s e he
  exact finiteLocallyFree_zeroScheme_on_smooth_open q j L s
    (zeroScheme_range_subset_of_boundary_frame i j hcover L s e he)

end Scheme.Modules

end AlgebraicGeometry
