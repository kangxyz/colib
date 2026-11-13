/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilEndpoints
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.HomotopyActions

/-!
# Transfer actions of the whole zero schemes at both ends of a retained pencil
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L]
  (a c : Γ(L, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "F" => Cor.nativeRetainedFamilySource (k := k) t q r L a c

/-- Homotopy invariance equates the transfer actions of the two actual
zero schemes, retaining both legs and the full fiber multiplicities. -/
theorem transfer_retainedZeroSchemes_eq
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant) :
    let f := F
    ∀ [hFamilyFin : IsFinite f] [hFamilyFlat : Flat f],
      let h₀ := Cor.nativeRetainedZero_finite_flat (k := k) t q r L a c
        (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
      let h₁ := Cor.nativeRetainedOne_finite_flat (k := k) t q r L a c
        (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
      transfer P (X := Cor.mk U) (Y := Cor.mk W)
          (Cor.retainedZeroSpan (k := k) t q r L a h₀.1 h₀.2) =
        transfer P (X := Cor.mk U) (Y := Cor.mk W)
          (Cor.retainedZeroSpan (k := k) t q r L c h₁.1 h₁.2) := by
  intro f hFin hFlat
  let δ : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W :=
    Cor.nativeRetainedFamilySpan (k := k) t q r L a c
      (_hFamilyFin := hFin) (_hFamilyFlat := hFlat)
  have h := transfer_homotopy_endpoints (k := k) P hP U (Cor.mk W) δ 0 1
  have h₀ := Cor.nativeRetainedFamily_zero (k := k) t q r L a c
    (hFamilyFin := hFin) (hFamilyFlat := hFlat)
  have h₁ := Cor.nativeRetainedFamily_one (k := k) t q r L a c
    (hFamilyFin := hFin) (hFamilyFlat := hFlat)
  let action (γ : Cor.mk U ⟶ Cor.mk W) := transfer P γ
  exact (congrArg action (Cor.NativeSectionSpanSpecialization.eq (k := k) h₀)).symm.trans
    (h.trans (congrArg action (Cor.NativeSectionSpanSpecialization.eq (k := k) h₁)))

end AlgebraicGeometry.PresheafWithTransfers
