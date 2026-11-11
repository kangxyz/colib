/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.Endpoints

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open SmoothSite.Contraction
open AlgebraicGeometry.PresheafWithTransfers

universe u v w

-- The ordinary endpoint assertion supports an arbitrary coefficient category.
example (R : CommRingCat.{u}) {A : Type w} [Category.{v} A]
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) (hP : A1.IsInvariant R P)
    (X : SmoothSite (Spec R)) (a b : R) :
    A1.sectionPullback R P X a = A1.sectionPullback R P X b :=
  A1.sectionPullback_eq R P hP X a b

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  (hP : IsA1Invariant P) (X Y : SmoothSite (Spec (.of k)))
  (α : Cor.mk (affineLineCylinder.obj X) ⟶ Cor.mk Y)

-- The sign is endpoint one minus endpoint zero, on the original graph maps.
example :
    transfer P (((Cor.graphFunctor k).map (nativeAffineSection (.of k) X 1) ≫ α) -
      ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X 0) ≫ α)) = 0 :=
  transfer_homotopy_endpoint_sub_eq_zero P hP X (Cor.mk Y) α 1 0

-- Composite exponent, with annihilation on the output group and no perfect-field assumption.
example (s t : X ⟶ Y) (c d : Cor.mk X ⟶ Cor.mk Y)
    (hn : ∀ x : sections P (Cor.mk X), (6 : ℤ) • x = 0)
    (h : (Cor.graphFunctor k).map s - (Cor.graphFunctor k).map t =
      (6 : ℤ) • (c - d) +
        (((Cor.graphFunctor k).map (nativeAffineSection (.of k) X 1) ≫ α) -
          ((Cor.graphFunctor k).map (nativeAffineSection (.of k) X 0) ≫ α))) :
    ((toPresheaf k).obj P).map s.op = ((toPresheaf k).obj P).map t.op :=
  restriction_eq_of_graph_sub_eq_zsmul_add_endpoint_sub P hP s t c d α 1 0 6 hn h
