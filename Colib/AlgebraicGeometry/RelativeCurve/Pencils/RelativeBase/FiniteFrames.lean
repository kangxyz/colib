/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteBoundaryFrames
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# Actual finite-neighborhood frames and one common principal base

The frame is lifted on an open scheme, not merely chosen on a residue fibre.
The native affine global-generation theorem produces a section nonvanishing at
an entire finite set. Finite closed-image avoidance then produces a neighborhood
of all specified target points. The second theorem chooses one principal base
neighborhood for two independent finite boundary schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.Ample Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

set_option maxHeartbeats 400000 in
-- The comparison unfolds the native module restriction on an affine chart.
/-- Native trivialization around a complete finite subset of an affine scheme. -/
theorem exists_affineModuleFrame_around_finite {X : Scheme.{u}} [IsAffine X]
    (L : X.Modules) [IsInvertibleModule X L] (E : Set X) (hE : E.Finite) :
    ∃ U : X.Opens, E ⊆ U ∧
      Nonempty (L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹IsInvertibleModule X L›
  let hX : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let f := hX.fromSpec
  have : IsOpenImmersion f := hX.isOpenImmersion_fromSpec
  have : Stacks.SheafOfModules.IsInvertible (Spec Γ(X, ⊤)).presheaf
      (structureSheafRing (Spec Γ(X, ⊤)).toRingedSpace).property (L.restrict f) := by
    have := Stacks.Modules.isInvertible_pullback f L
    exact Stacks.SheafOfModules.isInvertible_of_iso (Spec Γ(X, ⊤)).presheaf
      (structureSheafRing (Spec Γ(X, ⊤)).toRingedSpace).property
      ((Modules.restrictFunctorIsoPullback f).app L).symm
  have hE' : (f.base ⁻¹' E).Finite :=
    hE.preimage f.isOpenEmbedding.injective.injOn
  obtain ⟨s, hs, -⟩ := Modules.exists_sections_finite_subset_nonvanishingOpen_of_spec
    (L.restrict f) hE' ⊤ (fun _ _ => trivial)
  let N : (Spec Γ(X, ⊤)).Opens := Stacks.SheafOfModules.nonvanishingOpen
    (X := (Spec Γ(X, ⊤)).toRingedSpace) (L.restrict f) s
  let U := f ''ᵁ N
  have hEU : E ⊆ U := by
    intro x hx
    have hxTop : x ∈ (⊤ : X.Opens) := trivial
    rw [← hX.opensRange_fromSpec] at hxTop
    obtain ⟨y, hy⟩ := hxTop
    have hy' : f y = x := hy
    have hyE : f y ∈ E := hy'.symm ▸ hx
    exact ⟨y, hs hyE, hy⟩
  obtain ⟨eN⟩ := Stacks.SheafOfModules.nonempty_restrictIsoUnit_of_le_nonvanishingOpen
    (Spec Γ(X, ⊤)) (L.restrict f) s N le_rfl
  let e₀ : L.restrict (N.ι ≫ f) ≅ SheafOfModules.unit N.toScheme.ringCatSheaf :=
    (Modules.restrictFunctorComp N.ι f).app L ≪≫ eN
  exact ⟨U, hEU, ⟨Stacks.SheafOfModules.restrictIsoUnitOfIsoOver L (f.isoImage N)
    (Scheme.Hom.isoImage_hom_ι f N) e₀⟩⟩

/-- A finite morphism admits one actual frame above an entire finite target set.
The source need not be reduced or flat. -/
theorem exists_finiteTargetFrame_around_finite {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] (L : X.Modules) [IsInvertibleModule X L]
    (E : Set Y) (hE : E.Finite) :
    ∃ U : Y.Opens, E ⊆ U ∧
      Nonempty (L.restrict (f ⁻¹ᵁ U).ι ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let : IsAffine X := isAffine_of_isAffineHom f
  have hpre : (f ⁻¹' E).Finite := by
    convert hE.biUnion (fun y _ => f.finite_preimage_singleton y) using 1
    ext x
    simp
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_affineModuleFrame_around_finite L (f ⁻¹' E) hpre
  let U : Y.Opens := ⟨(f '' (W : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hUW : f ⁻¹ᵁ U ≤ W := by
    intro x hx
    change f x ∉ f '' (W : Set X)ᶜ at hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  refine ⟨U, ?_, ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L hUW e⟩⟩
  rintro y hy ⟨x, hx, rfl⟩
  exact hx (hW hy)

/-- The same frame can be chosen above a principal open containing every point
of the finite target set. -/
theorem exists_principalFiniteTargetFrame {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] (L : X.Modules) [IsInvertibleModule X L]
    (E : Set Y) (hE : E.Finite) :
    ∃ r : Γ(Y, ⊤), E ⊆ Y.basicOpen r ∧
      Nonempty (L.restrict (f ⁻¹ᵁ Y.basicOpen r).ι ≅
        SheafOfModules.unit (f ⁻¹ᵁ Y.basicOpen r).toScheme.ringCatSheaf) := by
  obtain ⟨U, hEU, ⟨e⟩⟩ := exists_finiteTargetFrame_around_finite f L E hE
  obtain ⟨r, hEr, hrU⟩ := Y.exists_basicOpen_subset_of_finite_of_isQuasiAffine hE U hEU
  exact ⟨r, hEr, ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L
    (fun _ hx => hrU hx) e⟩⟩

/-- Both independent finite boundaries are framed on the same actual principal
base neighborhood, before any source or Serre exponent is chosen. -/
theorem exists_commonPrincipalBoundaryFrames {S D Z : Scheme.{u}} [IsAffine S]
    (bD : D ⟶ S) [IsFinite bD] (bZ : Z ⟶ S) [IsFinite bZ]
    (MD : D.Modules) [IsInvertibleModule D MD]
    (MZ : Z.Modules) [IsInvertibleModule Z MZ]
    (x : S) (W : S.Opens) (hxW : x ∈ W) :
    ∃ r : Γ(S, ⊤), x ∈ S.basicOpen r ∧ S.basicOpen r ≤ W ∧
      Nonempty (MD.restrict (bD ⁻¹ᵁ S.basicOpen r).ι ≅
        SheafOfModules.unit (bD ⁻¹ᵁ S.basicOpen r).toScheme.ringCatSheaf) ∧
      Nonempty (MZ.restrict (bZ ⁻¹ᵁ S.basicOpen r).ι ≅
        SheafOfModules.unit (bZ ⁻¹ᵁ S.basicOpen r).toScheme.ringCatSheaf) := by
  obtain ⟨UD, hxD, ⟨eD⟩⟩ := exists_finiteTargetFrame_around_finite bD MD {x}
    (Set.finite_singleton x)
  obtain ⟨UZ, hxZ, ⟨eZ⟩⟩ := exists_finiteTargetFrame_around_finite bZ MZ {x}
    (Set.finite_singleton x)
  have hxu : x ∈ W ⊓ UD ⊓ UZ :=
    ⟨⟨hxW, hxD (Set.mem_singleton x)⟩, hxZ (Set.mem_singleton x)⟩
  obtain ⟨r, hxr, hr⟩ := S.exists_basicOpen_subset_of_finite_of_isQuasiAffine
    (Set.finite_singleton x) (W ⊓ UD ⊓ UZ)
    (Set.singleton_subset_iff.mpr hxu)
  refine ⟨r, hxr (Set.mem_singleton x), fun _ h => (hr h).1.1, ?_, ?_⟩
  · exact ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE MD (fun _ h => (hr h).1.2) eD⟩
  · exact ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE MZ (fun _ h => (hr h).2) eZ⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
