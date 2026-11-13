/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant

/-!
# Endpoint actions on homotopy-invariant transfer coefficients

Actual constant sections of the native affine cylinder have equal pullbacks on
homotopy-invariant coefficients. Consequently every signed finite correspondence
out of that cylinder has equal endpoint actions. The torsion consumer retains
the original graph maps and an explicit signed endpoint difference.

The section and transfer endpoint proofs adapt
`Motivic/Cohomology/A1/Basic.lean: sectionPullback_eq, transfer_homotopy_endpoints`
from the 2026-10-21 source checkpoint. The torsion calculation adapts
`Motivic/Transfers/Presheaf/Actions/Principal/TorsionSectionComparison.lean`.
Here all correspondences are the current native cycle subgroup, not the archived
Finsupp presentation. No principal-divisor family, moving theorem, sheafification
invariance or rigidity theorem is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u v w

namespace AlgebraicGeometry.A1
open _root_.AlgebraicGeometry.Scheme

variable (R : CommRingCat.{u}) {A : Type w} [Category.{v} A]

/-- Any two actual constant sections induce the same map on HI coefficients. -/
theorem sectionPullback_eq (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) (a b : R) :
    sectionPullback R P X a = sectionPullback R P X b := by
  let := hP X
  apply (cancel_epi (projectionPullback R P X)).mp
  rw [projectionPullback_sectionPullback, projectionPullback_sectionPullback]

end AlgebraicGeometry.A1

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable {k : Type u} [Field k]

/-- A genuine signed correspondence homotopy has equal endpoint actions.
The cylinder correspondence need not be the graph of a scheme morphism. -/
@[colib_tag "COL-1211", colib_ref "motivic_source_3df0a472"
  "Motivic/Cohomology/A1/Basic.lean:129-139"
  "ingredient" "Original HI transfer endpoint argument, adapted to native signed cycle \
    correspondences."]
theorem transfer_homotopy_endpoints (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (X : SmoothSite (Spec (.of k))) (Y : Cor k)
    (α : (Cor.graphFunctor k).obj (affineLineCylinder.obj X) ⟶ Y) (a b : k) :
    transfer P ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X a) ≫ α) =
      transfer P ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X b) ≫ α) := by
  rw [transfer_comp, transfer_comp]
  have h : transfer P ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X a)) =
      transfer P ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X b)) :=
    A1.sectionPullback_eq (.of k) ((toPresheaf k).obj P) hP X a b
  rw [h]

/-- The signed difference of the actual endpoints has zero transfer action. -/
theorem transfer_homotopy_endpoint_sub_eq_zero (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (X : SmoothSite (Spec (.of k))) (Y : Cor k)
    (α : (Cor.graphFunctor k).obj (affineLineCylinder.obj X) ⟶ Y) (a b : k) :
    transfer P (((Cor.graphFunctor k).map (nativeAffineSection (.of k) X a) ≫ α) -
      ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X b) ≫ α)) = 0 := by
  rw [transfer_sub, transfer_homotopy_endpoints P hP X Y α a b, sub_self]

/-- A literal graph relation modulo a multiple and an actual homotopy boundary
forces equality of the original ordinary restrictions. Annihilation is required
on the codomain of the contravariant action. The geometric relation remains an
explicit hypothesis; this theorem does not produce it from a tensor root. -/
theorem restriction_eq_of_graph_sub_eq_zsmul_add_endpoint_sub
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    {X Y : SmoothSite (Spec (.of k))} (s t : X ⟶ Y)
    (c d : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (α : (Cor.graphFunctor k).obj (affineLineCylinder.obj X) ⟶ (Cor.graphFunctor k).obj Y)
    (a b : k) (n : ℤ)
    (hn : ∀ x : sections P ((Cor.graphFunctor k).obj X), n • x = 0)
    (h : (Cor.graphFunctor k).map s - (Cor.graphFunctor k).map t =
      n • (c - d) +
        (((Cor.graphFunctor k).map (nativeAffineSection (.of k) X a) ≫ α) -
          ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X b) ≫ α))) :
    ((toPresheaf k).obj P).map s.op = ((toPresheaf k).obj P).map t.op := by
  change transfer P ((Cor.graphFunctor k).map s) =
    transfer P ((Cor.graphFunctor k).map t)
  apply sub_eq_zero.mp
  rw [← transfer_sub, h, transfer_add, transfer_zsmul,
    transfer_homotopy_endpoint_sub_eq_zero P hP X ((Cor.graphFunctor k).obj Y) α a b, add_zero]
  ext x
  change n • transfer P (c - d) x = 0
  exact hn _

end AlgebraicGeometry.PresheafWithTransfers
