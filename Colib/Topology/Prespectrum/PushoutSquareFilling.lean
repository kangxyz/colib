/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.Prespectrum.PushoutMovingHomotopy

/-!
# Square descent on the native reduced homotopy pushout

A continuous overlap cube with six prescribed faces descends with the two chart squares.
Its three cylinder parameters and the independent prespectrum structure time are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C D : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {a₀₀ a₀₁ a₁₀ a₁₁ : prespectrum f g ⟶ D}
  (H₀ : Homotopy a₀₀ a₀₁) (H₁ : Homotopy a₁₀ a₁₁)
  (L : Homotopy a₀₀ a₁₀) (M : Homotopy a₀₁ a₁₁)
  (SL : (Homotopy.precomp (inl f g) H₀).Square (Homotopy.precomp (inl f g) H₁)
    (Homotopy.precomp (inl f g) L) (Homotopy.precomp (inl f g) M))
  (SR : (Homotopy.precomp (inr f g) H₀).Square (Homotopy.precomp (inr f g) H₁)
    (Homotopy.precomp (inr f g) L) (Homotopy.precomp (inr f g) M))

/-- Six prescribed cube faces, the basepoint and an independent structure-time law. -/
structure SquareCylinder where
  /-- The actual joint three-parameter family on the original overlap source. -/
  level (n : ℕ) : C(unitInterval × (unitInterval × (unitInterval × A.space n)), D.space n)
  /-- The initial square face is the initial comparison on the original overlap. -/
  at_zero (n : ℕ) (s t : unitInterval) (x : A.space n) :
    level n (0, (s, (t, x))) = H₀.level n (s, cylinder f g n (t, x))
  /-- The final square face is the final comparison on the original overlap. -/
  at_one (n : ℕ) (s t : unitInterval) (x : A.space n) :
    level n (1, (s, (t, x))) = H₁.level n (s, cylinder f g n (t, x))
  /-- At original homotopy time zero keep the first moving side. -/
  bottom (n : ℕ) (r t : unitInterval) (x : A.space n) :
    level n (r, (0, (t, x))) = L.level n (r, cylinder f g n (t, x))
  /-- At original homotopy time one keep the second moving side. -/
  top (n : ℕ) (r t : unitInterval) (x : A.space n) :
    level n (r, (1, (t, x))) = M.level n (r, cylinder f g n (t, x))
  /-- At cylinder height zero keep the complete left-chart square. -/
  left (n : ℕ) (r s : unitInterval) (x : A.space n) :
    level n (r, (s, (0, x))) = SL.level n (r, (s, f.map n x))
  /-- At cylinder height one keep the complete right-chart square. -/
  right (n : ℕ) (r s : unitInterval) (x : A.space n) :
    level n (r, (s, (1, x))) = SR.level n (r, (s, g.map n x))
  /-- Keep the entire basepoint plane fixed. -/
  at_point (n : ℕ) (r s t : unitInterval) :
    level n (r, (s, (t, A.point n))) = D.point n
  /-- The spectrum structure time is independent of all three cube coordinates. -/
  comm (n : ℕ) (r s t : unitInterval) (x : A.space n) (z : unitInterval) :
    level (n + 1) (r, (s, (t, A.structureMap n x z))) =
      D.structureMap n (level n (r, (s, (t, x)))) z

variable (Q : SquareCylinder f g H₀ H₁ L M SL SR)

/-- The whole two-parameter value on each original pushout point. -/
def squareDescFamily (n : ℕ) : C(Space f g n, C(unitInterval × unitInterval, D.space n)) where
  toFun := Quot.lift (Sum.elim (Sum.elim
    (ContinuousMap.curry ⟨fun z : B.space n × (unitInterval × unitInterval) ↦
      SL.level n (z.2.1, (z.2.2, z.1)), by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : C.space n × (unitInterval × unitInterval) ↦
      SR.level n (z.2.1, (z.2.2, z.1)), by fun_prop⟩))
    (ContinuousMap.curry ⟨fun z : (unitInterval × A.space n) × (unitInterval × unitInterval) ↦
      Q.level n (z.2.1, (z.2.2, z.1)), by fun_prop⟩)) (by
      intro x y h
      cases h with
      | left x => ext z; exact Q.left n z.1 z.2 x
      | right x => ext z; exact Q.right n z.1 z.2 x
      | base t => ext z; exact (Q.at_point n z.1 z.2 t).trans (SL.at_point n z.1 z.2).symm)
  continuous_toFun := continuous_quot_lift _
    (((ContinuousMap.curry ⟨fun z : B.space n × (unitInterval × unitInterval) ↦
      SL.level n (z.2.1, (z.2.2, z.1)), by fun_prop⟩).continuous.sumElim
      (ContinuousMap.curry ⟨fun z : C.space n × (unitInterval × unitInterval) ↦
        SR.level n (z.2.1, (z.2.2, z.1)), by fun_prop⟩).continuous).sumElim
      (ContinuousMap.curry
        ⟨fun z : (unitInterval × A.space n) × (unitInterval × unitInterval) ↦
          Q.level n (z.2.1, (z.2.2, z.1)), by fun_prop⟩).continuous)

/-- The genuine cylinder cube and two complete chart squares descend to the whole square. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutSquareFilling.lean:80-119"
  "adaptation" "Whole square descends from the given native overlap cube and two chart squares."]
def squareOfCylinder : H₀.Square H₁ L M where
  level n := ⟨fun z ↦ squareDescFamily f g H₀ H₁ L M SL SR Q n z.2.2 (z.1, z.2.1),
    (squareDescFamily f g H₀ H₁ L M SL SR Q n).uncurry.continuous.comp
      (show Continuous (fun z : unitInterval × (unitInterval × Space f g n) ↦
        (z.2.2, (z.1, z.2.1))) by fun_prop)⟩
  at_zero n s q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact SL.at_zero n s x
        | inr x => exact SR.at_zero n s x
      | inr z => exact Q.at_zero n s z.1 z.2
  at_one n s q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact SL.at_one n s x
        | inr x => exact SR.at_one n s x
      | inr z => exact Q.at_one n s z.1 z.2
  left n r q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact SL.left n r x
        | inr x => exact SR.left n r x
      | inr z => exact Q.bottom n r z.1 z.2
  right n r q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact SL.right n r x
        | inr x => exact SR.right n r x
      | inr z => exact Q.top n r z.1 z.2
  at_point n r s := SL.at_point n r s
  comm n r s q t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact SL.comm n r s x t
        | inr x => exact SR.comm n r s x t
      | inr z => exact Q.comm n r s z.1 z.2 t

/-- The whole left chart square survives descent literally. -/
theorem squareOfCylinder_inl (n : ℕ) (r s : unitInterval) (x : B.space n) :
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level n (r, (s, (inl f g).map n x)) =
      SL.level n (r, (s, x)) := rfl

/-- The whole right chart square survives descent literally. -/
theorem squareOfCylinder_inr (n : ℕ) (r s : unitInterval) (x : C.space n) :
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level n (r, (s, (inr f g).map n x)) =
      SR.level n (r, (s, x)) := rfl

/-- The entire inner cube is retained with all three original coordinates. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutSquareFilling.lean:132-135"
  "adaptation" "Retain all three actual cylinder coordinates at each original level."]
theorem squareOfCylinder_cylinder (n : ℕ) (r s t : unitInterval) (x : A.space n) :
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level n (r, (s, cylinder f g n (t, x))) =
      Q.level n (r, (s, (t, x))) := rfl

end Topology.LoopPrespectrum.HomotopyPushout
