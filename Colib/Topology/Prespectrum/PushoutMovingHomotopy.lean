/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.HomotopySquare

/-! # Pushout descent of continuous squares with moving endpoints

The supplied square and its two moving endpoint tracks descend through the actual reduced
homotopy pushout. Currying in the interval parameter precedes quotient descent; evaluation then
produces the homotopy, with no local compactness assumption on any prespectrum level.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/PushoutMovingHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C D : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {b₀ b₁ : B ⟶ D} {c₀ c₁ : C ⟶ D}
  {H₀ : Homotopy (f ≫ b₀) (g ≫ c₀)} {H₁ : Homotopy (f ≫ b₁) (g ≫ c₁)}
  (L : Homotopy b₀ b₁) (M : Homotopy c₀ c₁)
  (S : H₀.Square H₁ (Homotopy.precomp f L) (Homotopy.precomp g M))

/-- The supplied cylinder square, curried in the independent comparison parameter. -/
def descSquarePiece (n : ℕ) : C(unitInterval × A.space n, C(unitInterval, D.space n)) :=
  ContinuousMap.curry ⟨fun z ↦ S.level n (z.2, z.1), by fun_prop⟩

/-- The actual interval-valued quotient map includes both moving endpoint tracks. -/
def descSquareFamily (n : ℕ) : C(Space f g n, C(unitInterval, D.space n)) where
  toFun := Quot.lift (Sum.elim
    (Sum.elim
      (ContinuousMap.curry ⟨fun z : B.space n × unitInterval ↦ L.level n (z.2, z.1), by fun_prop⟩)
      (ContinuousMap.curry ⟨fun z : C.space n × unitInterval ↦ M.level n (z.2, z.1), by fun_prop⟩))
    (descSquarePiece f g L M S n)) (by
      intro x y h
      cases h with
      | left x => ext r; exact S.left n r x
      | right x => ext r; exact S.right n r x
      | base s => ext r; exact (S.at_point n r s).trans (L.at_point n r).symm)
  continuous_toFun := continuous_quot_lift _
    (((ContinuousMap.curry
      ⟨fun z : B.space n × unitInterval ↦ L.level n (z.2, z.1), by fun_prop⟩).continuous.sumElim
      (ContinuousMap.curry
      ⟨fun z : C.space n × unitInterval ↦ M.level n (z.2, z.1), by fun_prop⟩).continuous).sumElim
      (descSquarePiece f g L M S n).continuous)

/-- A genuine moving-boundary square induces a homotopy between the original descended maps. -/
def descSquareHomotopy : Homotopy (desc f g b₀ c₀ H₀) (desc f g b₁ c₁ H₁) where
  level n := ⟨fun z ↦ descSquareFamily f g L M S n z.2 z.1,
    (descSquareFamily f g L M S n).uncurry.continuous.comp continuous_swap⟩
  at_zero n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl y => exact L.at_zero n y
        | inr z => exact M.at_zero n z
      | inr z => exact S.at_zero n z.1 z.2
  at_one n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl y => exact L.at_one n y
        | inr z => exact M.at_one n z
      | inr z => exact S.at_one n z.1 z.2
  at_point n r := L.at_point n r
  comm n r q t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl y => exact L.comm n r y t
        | inr z => exact M.comm n r z t
      | inr z => exact S.comm n r z.1 z.2 t

/-- The entire left boundary is precisely the supplied moving left endpoint track. -/
@[simp] theorem descSquareHomotopy_inl (n : ℕ) (r : unitInterval) (y : B.space n) :
    (descSquareHomotopy f g L M S).level n (r, (inl f g).map n y) = L.level n (r, y) := rfl

/-- The entire right boundary is precisely the supplied moving right endpoint track. -/
@[simp] theorem descSquareHomotopy_inr (n : ℕ) (r : unitInterval) (z : C.space n) :
    (descSquareHomotopy f g L M S).level n (r, (inr f g).map n z) = M.level n (r, z) := rfl

/-- Every point of the actual double cylinder retains both independent parameters. -/
@[simp] theorem descSquareHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : A.space n) :
    (descSquareHomotopy f g L M S).level n (r, cylinder f g n (s, x)) =
      S.level n (r, (s, x)) := rfl

/-- Each time slice is the descent of the actual corresponding moving overlap track. -/
theorem descSquareHomotopy_at (r : unitInterval) :
    (descSquareHomotopy f g L M S).at r = desc f g (L.at r) (M.at r) (S.at r) := by
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

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutMovingHomotopy.lean:32-98"
  "adaptation" "Whole moving-boundary quotient descent by currying into continuous interval maps"]
  Topology.LoopPrespectrum.HomotopyPushout.descSquareHomotopy
