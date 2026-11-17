/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ParameterOrientation

/-!
# Trivial-bundle Thom classes and their parameter changes

An integral parameter acts trivially on the weight-zero class obtained by
cancelling the common Tate factor. In particular, restrictions at two
sections of an integral family of linear frame changes give the same
normalized supported class. The proof uses the actual pair-triangle maps
and a natural comparison with the corresponding Tate powers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "B" => SmoothSite.base S
local notation "M" => effectiveSmoothMotive k
local notation "E" => EffectiveMotivesMinus k

variable (c : ℕ)

local notation "F" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) c

/-- Two parameter sections with integral common target induce equal restrictions on
every supported class after cancelling the finite Lefschetz power. -/
theorem iterateLefschetz_baseHom_precomp_eq {X Y : Sm} [IsIntegral Y.left]
    (f g : X ⟶ Y) (v : (F).obj ((M).obj Y) ⟶ (F).obj ((M).obj B)) :
    (F).map ((M).map f) ≫ v = (F).map ((M).map g) ≫ v := by
  let e := (effectiveReducedTorusTensorFullyFaithful k).comp
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor E (1 : ℤ)))
  let : (effectiveLefschetzTwistFunctor k).Full := e.full
  let : (effectiveLefschetzTwistFunctor k).Faithful := e.faithful
  let u := Functor.FullyFaithful.ofFullyFaithful F
  let a := u.preimage v
  rw [← u.map_preimage v, ← (F).map_comp, ← (F).map_comp,
    effectiveSmoothMotive_baseHom_precomp_eq k f g a]

/-- Equal restrictions on a Tate power may be transported through an
isomorphism identifying the parameter motive with that power. -/
theorem iterateLefschetz_baseHom_precomp_eq_of_iso {X Y : Sm} [IsIntegral Y.left]
    (f g : X ⟶ Y) {P Q : E} (u : P ⟶ (F).obj ((M).obj X))
    (e : Q ≅ (F).obj ((M).obj Y)) (a b : P ⟶ Q)
    (ha : a ≫ e.hom = u ≫ (F).map ((M).map f))
    (hb : b ≫ e.hom = u ≫ (F).map ((M).map g))
    (q : Q ⟶ (F).obj ((M).obj B)) :
    a ≫ q = b ≫ q := by
  let v := e.inv ≫ q
  have hq : e.hom ≫ v = q := e.hom_inv_id_assoc q
  have h (m : P ⟶ Q) (r : X ⟶ Y) (hm : m ≫ e.hom = u ≫ (F).map ((M).map r)) :
      m ≫ q = u ≫ (F).map ((M).map r) ≫ v :=
    (congrArg (m ≫ ·) hq.symm).trans ((Category.assoc m e.hom v).symm.trans
      ((congrArg (· ≫ v) hm).trans (Category.assoc u ((F).map ((M).map r)) v)))
  exact (h a f ha).trans
    ((congrArg (u ≫ ·) (iterateLefschetz_baseHom_precomp_eq k c f g v)).trans (h b g hb).symm)

end AlgebraicGeometry.MotivicHomotopy
