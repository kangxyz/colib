/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.DisjointUnions

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u v

variable {k : Type u} [Field k]
  (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})

example (X : Cor k) [IsEmpty X.toSmoothSite.left] (s : E ⟶ F.obj (op X)) : s = 0 :=
  PresheafWithTransfers.section_eq_zero_of_isEmpty F E X s

example (X Y : Cor k) :
    Function.Bijective (fun s : E ⟶ F.obj (op (Cor.coproduct k X Y)) =>
      (s ≫ F.map (Cor.coproductInl k X Y).op,
        s ≫ F.map (Cor.coproductInr k X Y).op)) :=
  PresheafWithTransfers.binaryCoproduct_sections_bijective F E X Y

example {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    Function.Bijective (fun s : E ⟶ F.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) =>
      fun i => s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i)).op) :=
  PresheafWithTransfers.finiteCoproduct_sections_bijective F E Y
