/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.VectorBundleFrameChange
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-! # Finite covers by affine normal-bundle charts -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open SmoothSite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "E₀" => (Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules)

/-- The intersection of affine opens in the original separated smooth scheme is affine. -/
theorem isAffineOpen_smooth_intersection {Y : Sm} (U V : Y.left.affineOpens) :
    IsAffineOpen (U.1 ⊓ V.1) := by
  let f : Y.left ⟶ S := Y.hom
  let : IsAffine S := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  have hh : IsAffineHom (pullback.diagonal f) := inferInstance
  exact (isAffineHom_diagonal_iff (f := f)).mp hh ⊤ (isAffineOpen_top S)
    U.1 (by simp) V.1 (by simp) U.2 V.2

include hX hZ in
/-- The normal chart can be chosen within the integral component of its marked point. -/
theorem exists_integral_normalBundleBasisChart (x : Z.left) :
    ∃ V : Z.left.affineOpens, x ∈ V.1 ∧ IsIntegral V.1.toScheme ∧
      Nonempty (Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) := by
  obtain ⟨V, hx, hb⟩ := exists_normalBundleBasisChart i hX hZ x
  let C := componentOpen k Z _ (irreducibleComponent_mem_irreducibleComponents x)
  have hxC : x ∈ C := mem_irreducibleComponent
  obtain ⟨W, hWa, hxW, hW⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V.1 ⊓ C from ⟨hx, hxC⟩)
  let U := (⟨W, hWa⟩ : Z.left.affineOpens)
  let f := Z.left.homOfLE (hW.trans inf_le_right)
  let : IsIntegral C.toScheme :=
    isIntegral_componentOpen k Z _
      (irreducibleComponent_mem_irreducibleComponents x)
  let : Nonempty W.toScheme := ⟨⟨x, hxW⟩⟩
  exact ⟨U, hxW, isIntegral_of_isOpenImmersion f,
    hb.map (fun b => Scheme.Modules.vectorBundleBasisRestrict E₀ b (hW.trans inf_le_left))⟩

include hX hZ in
/-- A finite cover by affine basis charts with integral bases. -/
theorem exists_finset_integral_normalBundleBasisCover :
    ∃ V : Z.left → Z.left.affineOpens,
      ∃ _b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1),
        ∃ ts : Finset Z.left, ts.sup (fun x => (V x).1) = ⊤ ∧
          ∀ x, IsIntegral (V x).1.toScheme := by
  classical
  have h (x : Z.left) := exists_integral_normalBundleBasisChart k i hX hZ x
  choose V hv hi hb using h
  let C (x : Z.left) := (V x).1
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace (Y := S) Z.hom
  have htop : (⨆ x, C x) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hv x⟩
  have hcompact : IsCompactElement (⊤ : Z.left.Opens) :=
    (TopologicalSpace.Opens.isCompactElement_iff _).mpr isCompact_univ
  obtain ⟨ts, hts⟩ := (isCompactElement_iff_exists_le_iSup_of_le_iSup _).mp hcompact
    Z.left C (by rw [htop])
  exact ⟨V, fun x => (hb x).some, ts, top_unique hts, hi⟩

end AlgebraicGeometry.MotivicHomotopy
