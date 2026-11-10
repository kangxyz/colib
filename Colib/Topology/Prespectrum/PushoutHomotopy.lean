/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.RelativeHomotopy

/-!
# Homotopies between homotopy-pushout descents

A supplied two-parameter homotopy between the original overlap tracks, relative to their endpoints
and basepoint line, gives a whole coherent homotopy between the corresponding pushout maps. The
endpoint arrows are fixed. The actual comparison family is curried into the compact-open interval
mapping space before quotient descent, then evaluated; no product-of-quotient assertion is used.

This transports given higher coherence. It does not assert that arbitrary geometric tracks admit
such a comparison, nor construct a Bass tower or a stable cofiber equivalence.
-/

@[expose] public section

noncomputable section


open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum.HomotopyPushout

variable {A B C D : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (b : B ⟶ D) (c : C ⟶ D)
  {H K : Homotopy (f ≫ b) (g ≫ c)} (J : H.RelHomotopy K)

/-- The actual two-parameter cylinder comparison, curried in comparison time. -/
def descHomotopyPiece (n : ℕ) : C(unitInterval × A.space n, C(unitInterval, D.space n)) :=
  ContinuousMap.curry ⟨fun z ↦ J.level n (z.2, z.1), by fun_prop⟩

/-- The interval-valued comparison family on the actual reduced pushout quotient. -/
def descHomotopyFamily (n : ℕ) : C(Space f g n, C(unitInterval, D.space n)) where
  toFun := Quot.lift (Sum.elim
    (Sum.elim (fun y ↦ ContinuousMap.const _ (b.map n y))
      (fun z ↦ ContinuousMap.const _ (c.map n z)))
    (descHomotopyPiece f g b c J n)) (by
      intro x y h
      cases h with
      | left x =>
        ext r
        exact (J.at r).at_zero n x
      | right x =>
        ext r
        exact (J.at r).at_one n x
      | base s =>
        ext r
        exact ((J.at r).at_point n s).trans (b.map_point n).symm)
  continuous_toFun := continuous_quot_lift _
    ((((ContinuousMap.curry ⟨fun z : B.space n × unitInterval ↦ b.map n z.1,
      by fun_prop⟩).continuous).sumElim
      ((ContinuousMap.curry ⟨fun z : C.space n × unitInterval ↦ c.map n z.1,
        by fun_prop⟩).continuous)).sumElim (descHomotopyPiece f g b c J n).continuous)

/-- Fixed-endpoint relative track comparisons induce actual coherent homotopies of descents. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutHomotopy.lean:64-92"
  "adaptation" "The original quotient descent of a relative two-parameter track"]
def descHomotopy : Homotopy (desc f g b c H) (desc f g b c K) where
  level n := ⟨fun z ↦ descHomotopyFamily f g b c J n z.2 z.1,
    (descHomotopyFamily f g b c J n).uncurry.continuous.comp continuous_swap⟩
  at_zero n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl y => rfl
        | inr z => rfl
      | inr z => exact (J.level n).apply_zero z
  at_one n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl y => rfl
        | inr z => rfl
      | inr z => exact (J.level n).apply_one z
  at_point n _r := b.map_point n
  comm n r q t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl y => exact congrArg (fun p ↦ p t) (b.comm n y)
        | inr z => exact congrArg (fun p ↦ p t) (c.comm n z)
      | inr z => exact J.comm n r z.1 z.2 t

/-- The left endpoint arrow stays fixed throughout the constructed comparison. -/
@[simp]
theorem descHomotopy_inl (n : ℕ) (r : unitInterval) (y : B.space n) :
    (descHomotopy f g b c J).level n (r, (inl f g).map n y) = b.map n y := rfl

/-- The right endpoint arrow stays fixed throughout the constructed comparison. -/
@[simp]
theorem descHomotopy_inr (n : ℕ) (r : unitInterval) (z : C.space n) :
    (descHomotopy f g b c J).level n (r, (inr f g).map n z) = c.map n z := rfl

/-- Both original homotopy parameters are retained on every cylinder point. -/
@[simp]
theorem descHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : A.space n) :
    (descHomotopy f g b c J).level n (r, cylinder f g n (s, x)) =
      J.level n (r, (s, x)) := rfl

/-- Every comparison-time slice is descent through its actual original overlap homotopy. -/
theorem descHomotopy_at (r : unitInterval) :
    (descHomotopy f g b c J).at r = desc f g b c (J.at r) := by
  apply hom_ext
  · apply Hom.ext
    funext n
    ext y
    rfl
  · apply Hom.ext
    funext n
    ext z
    rfl
  · intro n s x
    rfl

end Topology.LoopPrespectrum.HomotopyPushout
