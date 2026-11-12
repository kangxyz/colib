/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyHomotopy
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.HomotopyActions

/-! # Principal-order correspondences act trivially on homotopy-invariant presheaves

The boundary condition is imposed on the actual boundary scheme. The
interpolation retains all finite scheme-theoretic supports at both ends.

Adapted from `Motivic/Transfers/Presheaf/Actions/Principal/{Family,Open}.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.Cor.PrincipalOrder

/-- The principal correspondence of an original unit congruent to one
along the whole prescribed boundary acts by zero. -/
theorem transfer_principalOrder_open_eq_zero
    {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    {C V B : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [IsNoetherian V] [V.IsQuasiAffine]
    (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (W : C.Opens) [Nonempty W] (r : Γ(C, W)) (hr : IsUnit r)
    (b : B ⟶ W.toScheme) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι)) (hb : b.appTop (W.topIso.inv r) = 1)
    (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom) :
    transfer P (correspondence q j W (canonical_boundary_cover j W b hcover)
      r hr g hbase) = 0 := by
  let hW := canonical_boundary_cover j W b hcover
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    let : IsIntegral V := isIntegral_of_isOpenImmersion j
    let Y₀ := retainedSite X q j
    let e : Y₀ ⟶ Y := SmoothSite.homMk g hbase.symm
    let β : Cor.mk X ⟶ Cor.mk Y₀ :=
      correspondence (X := X) (Y := Y₀) q j W hW r hr (𝟙 V) (retainedIdentityBase X q j)
    obtain ⟨α, h0, h1⟩ := exists_familyCorrespondence_retained_endpoints X q j W r b hcover hb hr
    let δ : Cor.mk (affineLineCylinder.obj X) ⟶ Cor.mk Y₀ :=
      (Cor.graphFunctor k).map (affineCylinderPolynomialIso (.of k) X).hom ≫ α
    have hsection (a : k) :
        (Cor.graphFunctor k).map (nativeAffineSection (.of k) X a) ≫ δ =
          (Cor.graphFunctor k).map (polynomialAffineSection (.of k) X a) ≫ α := by
      dsimp only [δ]
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, nativeAffineSection_polynomialIso]
    have h := transfer_homotopy_endpoints P hP X (Cor.mk Y₀) δ 0 1
    rw [hsection 0, hsection 1, h0, h1, transfer_zero] at h
    have hβ : transfer P β = 0 := h.symm
    have hg : β ≫ (Cor.graphFunctor k).map e = correspondence q j W hW r hr g hbase :=
      correspondence_comp_graph (X := X) (Y := Y₀) (Z := Y)
        q j W hW r hr (𝟙 V) (retainedIdentityBase X q j)
        e g (Category.id_comp _) hbase
    rw [← hg, transfer_comp, hβ, comp_zero]
  · let : IsEmpty V := ⟨fun x => hV ⟨x⟩⟩
    rw [correspondence_eq_zero_of_isEmpty, transfer_zero]

end AlgebraicGeometry.PresheafWithTransfers
