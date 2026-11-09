/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.Cokernels

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

variable {k : Type u} [Field k]

example {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) (X : Cor k) :
    PresheafWithTransfers.sections (cokernel η) X ≅
      AddCommGrpCat.of (PresheafWithTransfers.sections Q X ⧸ (η.hom.app (op X)).hom.range) :=
  PresheafWithTransfers.cokernelSectionsIsoQuotient η X

example {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) (X : Cor k) :
    Function.Surjective ((cokernel.π η).hom.app (op X)) :=
  PresheafWithTransfers.cokernel_π_app_surjective η X

example {P Q : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}} [Q.Additive]
    (η : P ⟶ Q) : (cokernel η).Additive :=
  Functor.cokernel_additive η

example {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) (X : Cor k) :
    (cokernel.π η).hom.app (op X) ≫
      (PresheafWithTransfers.cokernelSectionsIsoQuotient η X).hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' (η.hom.app (op X)).hom.range) :=
  PresheafWithTransfers.cokernel_π_sectionsIsoQuotient_hom η X
