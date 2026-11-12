/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialTorsion

/-! # Original radicial graph pullback and full-degree torsion regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.PresheafWithTransfers

universe v u

variable {k : Type u} [Field k]

example {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f] [UniversallyInjective f]
    (g : B ⟶ Spec (.of k)) (a : A) (p : ℕ) [ExpChar k p] :
    ∃ r : ℕ, f.residueDegree a = p ^ r :=
  f.residueDegree_eq_pow_of_expChar g a p

example [CharZero k] {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f]
    [UniversallyInjective f] (g : B ⟶ Spec (.of k)) (a : A) :
    f.residueDegree a = 1 :=
  f.residueDegree_eq_one_of_charZero g a

example {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f] [UniversallyInjective f]
    (g : B ⟶ Spec (.of k)) (a : A) (n : ℕ) (hn : IsUnit (n : k)) :
    (f.residueDegree a).Coprime n :=
  f.residueDegree_coprime_of_isUnit g a n hn

variable (P : PresheafWithTransfers.{v} k)
  {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)
  [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]
  [UniversallyInjective q.left] (n : ℕ)
  (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
  (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ))

example (hcop : (q.left.residueDegree (genericPoint X.left)).Coprime n) :
    (radicialGraphIsoOfCoprime P q n hX hY hcop).hom =
      ((toPresheaf k).obj P).map q.op := rfl

example (hcop : (q.left.residueDegree (genericPoint X.left)).Coprime n) :
    (radicialGraphIsoOfCoprime P q n hX hY hcop).inv =
      Nat.gcdA (q.left.residueDegree (genericPoint X.left)) n •
        transfer P (Cor.finiteFlatTranspose k q) := rfl

include hX hY in
example (hn : IsUnit (n : k)) :
    ((toPresheaf k).obj P).map q.op ≫
        (Nat.gcdA (q.left.residueDegree (genericPoint X.left)) n •
          transfer P (Cor.finiteFlatTranspose k q)) = 𝟙 (sections P (Cor.mk Y)) :=
  (radicialGraphIso P q n hn hX hY).hom_inv_id

include hX hY in
example (hn : IsUnit (n : k)) :
    (Nat.gcdA (q.left.residueDegree (genericPoint X.left)) n •
          transfer P (Cor.finiteFlatTranspose k q)) ≫
        ((toPresheaf k).obj P).map q.op = 𝟙 (sections P (Cor.mk X)) :=
  (radicialGraphIso P q n hn hX hY).inv_hom_id

include hX hY in
example (hn : IsUnit (n : k)) : IsIso (((toPresheaf k).obj P).map q.op) :=
  isIso_toPresheaf_map_of_radicial P q n hn hX hY

#print axioms AlgebraicGeometry.Scheme.Hom.residueDegree_eq_pow_of_expChar
#print axioms AlgebraicGeometry.Scheme.Hom.residueDegree_eq_one_of_charZero
#print axioms AlgebraicGeometry.Scheme.Hom.residueDegree_coprime_of_isUnit
#print axioms AlgebraicGeometry.PresheafWithTransfers.radicialGraphIsoOfCoprime
#print axioms AlgebraicGeometry.PresheafWithTransfers.radicialGraphIso
#print axioms AlgebraicGeometry.PresheafWithTransfers.isIso_toPresheaf_map_of_radicial
