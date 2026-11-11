/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinarySource

/-! Regression consumers for the actual ordinary free source and sheafified identity cycle. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.SheafWithTransfers
open Stacks.Cohomology.FreeYonedaUnivLE
universe u

variable (k : Type u) [Field k]

-- This interface needs no HasExt or transfer-injective acyclicity.
example (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k) :
    ((transferRepresentable k).obj (Cor.mk X) ⟶ F) ≃+
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))).obj X ⟶
        (toSheaf k).obj F) :=
  ordinaryTransferHomEquiv k X F

example (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    ordinaryTransferHomEquiv k X F f =
      ordinaryToTransferSource k X ≫ (toSheaf k).map f :=
  ordinaryTransferHomEquiv_apply k X F f

example (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    sectionsAddEquiv.{u + 1} X ((toSheaf k).obj F)
        (ordinaryTransferHomEquiv k X F f) =
      transferSectionsEquiv k (Cor.mk X) F f :=
  ordinaryTransferHomEquiv_sections k X F f

example {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (freeYoneda.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))).map f ≫
        ordinaryToTransferSource k Y =
      ordinaryToTransferSource k X ≫
        (toSheaf k).map ((transferRepresentable k).map ((Cor.graphFunctor k).map f)) :=
  ordinaryToTransferSource_naturality k f

