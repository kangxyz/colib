/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.DoldKan.NormalizedRepresentatives

/-!
# Operations on normalized cycles

A simplicial map and subtraction preserve vanishing on the original faces.
The inclusion into the alternating face complex sends these elements to cycles.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace AlgebraicTopology.NormalizedMooreComplex

variable (X : SimplicialObject AddCommGrpCat.{u})

local notation "N(" Z ")" => Functor.obj (normalizedMooreComplex AddCommGrpCat) Z
local notation "A(" Z ")" => Functor.obj (alternatingFaceMapComplex AddCommGrpCat) Z
local notation "ι(" Z "," n ")" => HomologicalComplex.Hom.f (inclusionOfMooreComplexMap Z) n

/-- Every cycle is normalized. -/
theorem IsCycle.isNormalized {n : ℕ} {x : X.obj (op ⦋n⦌)} (hx : IsCycle X n x) :
    IsNormalized X n x := by
  cases n with
  | zero => trivial
  | succ n => exact fun i => hx i.succ

/-- A difference of cycles is killed by all the faces. -/
theorem IsCycle.sub {n : ℕ} {x y : X.obj (op ⦋n⦌)} (hx : IsCycle X n x)
    (hy : IsCycle X n y) : IsCycle X n (x - y) := by
  cases n with
  | zero => trivial
  | succ n =>
    intro i
    simp only [map_sub, hx i, hy i, sub_zero]

/-- A simplex killed by all faces is a cycle in the actual alternating face complex. -/
theorem alternatingCycle_of_isCycle (n : ℕ) (x : X.obj (op ⦋n⦌)) (hx : IsCycle X n x) :
    ((A(X)).sc n).g x = 0 := by
  obtain ⟨z, rfl⟩ := exists_inclusion_eq_of_isNormalized X n x (hx.isNormalized X)
  have hz := (isCycle_inclusion_iff X n z).1 hx
  let m := (ComplexShape.down ℕ).next n
  have h := ConcreteCategory.congr_hom ((inclusionOfMooreComplexMap X).comm n m) z
  change (A(X)).d n m (ι(X, n) z) = ι(X, m) ((N(X)).d n m z) at h
  change (N(X)).d n m z = 0 at hz
  exact h.trans ((congrArg (ι(X, m)) hz).trans (map_zero _))

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- A simplicial morphism preserves the condition of being killed by all faces. -/
theorem IsCycle.map (f : X ⟶ Y) {n : ℕ} {x : X.obj (op ⦋n⦌)} (hx : IsCycle X n x) :
    IsCycle Y n (f.app (op ⦋n⦌) x) := by
  cases n with
  | zero => trivial
  | succ n =>
    intro i
    have h := ConcreteCategory.congr_hom (f.naturality (SimplexCategory.δ i).op) x
    change f.app (op ⦋n⦌) (X.δ i x) = Y.δ i (f.app (op ⦋n + 1⦌) x) at h
    exact h.symm.trans (by simp only [hx i, map_zero])

end AlgebraicTopology.NormalizedMooreComplex
