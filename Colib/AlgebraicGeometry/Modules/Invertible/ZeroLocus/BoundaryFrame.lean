/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalBoundarySupport
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# Whole zero schemes of sections with prescribed boundary frame

A frame carrying the pulled-back section to one makes the inverse-image zero ideal the
unit ideal on the original boundary, including its nilpotents. If the complement is
contained in a quasi-affine open of a proper scheme over an affine base, the whole zero
scheme is finite. No regularity or flatness is assumed or asserted here.

This is the boundary-avoidance part of the prescribed-divisor construction in
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Sections/DivisorPairs/Serre.lean` from the
2026-10-21 checkpoint, now using native section and zero-ideal carriers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A section sent to one by a frame has the unit zero ideal, scheme-theoretically. -/
theorem zeroScheme_eq_top_of_frame {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (e : L ≅ SheafOfModules.unit X.ringCatSheaf)
    (he : Hom.app e.hom ⊤ s = (1 : Γ(X, ⊤))) : zeroScheme X L s = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply (Ideal.eq_top_iff_one _).mpr
  rw [zeroScheme_ideal]
  apply Ideal.subset_span
  refine ⟨{ toFun := Hom.app e.hom U.1
            map_add' := map_add _
            map_smul' := Hom.app_smul e.hom }, ?_⟩
  change (1 : Γ(X, U.1)) = Hom.app e.hom U.1 (L.presheaf.map (homOfLE le_top).op s)
  have h := PresheafOfModules.naturality_apply e.hom.val (homOfLE (le_top : U.1 ≤ ⊤)).op s
  exact ((map_one (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom).symm.trans
    (congrArg (fun t =>
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom t) he).symm).trans h.symm

/-- A prescribed frame equation on the full boundary annihilates its inverse-image zero
scheme. The boundary need not be reduced, flat or a closed immersion. -/
theorem zeroScheme_comap_eq_top_of_boundary_frame {X B : Scheme.{u}}
    (i : B ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : Hom.app e.hom ⊤ (pullbackGlobalSections i L s) = (1 : Γ(B, ⊤))) :
    (zeroScheme X L s).comap i = ⊤ := by
  rw [← zeroScheme_pullback i L s]
  exact zeroScheme_eq_top_of_frame _ _ e he

/-- The whole native zero scheme lies in the retained open, from its prescribed boundary
value. This does not replace the closed subscheme by its reduced support. -/
theorem zeroScheme_range_subset_of_boundary_frame {X B U : Scheme.{u}}
    (i : B ⟶ X) (j : U ⟶ X)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : Hom.app e.hom ⊤ (pullbackGlobalSections i L s) = (1 : Γ(B, ⊤))) :
    Set.range (zeroScheme X L s).subschemeι ⊆ Set.range j := by
  intro x hx
  rcases hcover x with hj | ⟨b, rfl⟩
  · exact hj
  · have hb : b ∈ ((zeroScheme X L s).comap i).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change i b ∈ (zeroScheme X L s).support
      exact Eq.mp
        (congrArg (fun A : Set X => i b ∈ A)
          (Scheme.IdealSheafData.range_subschemeι (zeroScheme X L s))) hx
    rw [zeroScheme_comap_eq_top_of_boundary_frame i L s e he] at hb
    exact False.elim hb

/-- Properness and a quasi-affine complement turn a prescribed boundary frame into
finiteness of the original zero scheme over the original affine base. -/
theorem isFinite_zeroScheme_of_boundary_frame {X B U S : Scheme.{u}}
    [IsAffine S] [U.IsQuasiAffine] (q : X ⟶ S) [IsProper q]
    (i : B ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : Hom.app e.hom ⊤ (pullbackGlobalSections i L s) = (1 : Γ(B, ⊤))) :
    IsFinite ((zeroScheme X L s).subschemeι ≫ q) :=
  Scheme.isFinite_closed_support_in_quasiAffine_open q j _
    (zeroScheme_range_subset_of_boundary_frame i j hcover L s e he)

end AlgebraicGeometry.Scheme.Modules
