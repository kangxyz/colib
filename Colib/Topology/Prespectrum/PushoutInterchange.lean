/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Interchange of two original reduced homotopy pushouts

A strict three-by-three span grid has index 0 for its common source, 1 for its left
and 2 for its right target, in each dimension. Its only compatibility inputs are
the four strict corner squares. The actual iterated reduced pushouts admit a
coordinate interchange. The full overlap square is constructed from the two
original cylinders, with independent interval times and structure-loop time.
Currying before quotient descent requires no local compactness, separation, or
point extension property of the prespectrum levels.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout

/-- Nine actual prespectra, twelve arrows, and the four local strict span squares. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:32"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
structure SpanGrid where
  /-- Index 0 denotes the common source, 1 the left target, and 2 the right target. -/
  obj : Fin 3 → Fin 3 → LoopPrespectrum.{u}
  /-- Left arrows within each row. -/
  horizontalLeft (i : Fin 3) : obj i 0 ⟶ obj i 1
  /-- Right arrows within each row. -/
  horizontalRight (i : Fin 3) : obj i 0 ⟶ obj i 2
  /-- Left arrows within each column. -/
  verticalLeft (j : Fin 3) : obj 0 j ⟶ obj 1 j
  /-- Right arrows within each column. -/
  verticalRight (j : Fin 3) : obj 0 j ⟶ obj 2 j
  left_left : horizontalLeft 0 ≫ verticalLeft 1 = verticalLeft 0 ≫ horizontalLeft 1
  left_right : horizontalRight 0 ≫ verticalLeft 2 = verticalLeft 0 ≫ horizontalRight 1
  right_left : horizontalLeft 0 ≫ verticalRight 1 = verticalRight 0 ≫ horizontalLeft 2
  right_right : horizontalRight 0 ≫ verticalRight 2 = verticalRight 0 ≫ horizontalRight 2

namespace SpanGrid

/-- Exchange the two literal span directions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:51"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def transpose (G : SpanGrid.{u}) : SpanGrid.{u} where
  obj i j := G.obj j i
  horizontalLeft := G.verticalLeft
  horizontalRight := G.verticalRight
  verticalLeft := G.horizontalLeft
  verticalRight := G.horizontalRight
  left_left := G.left_left.symm
  left_right := G.right_left.symm
  right_left := G.left_right.symm
  right_right := G.right_right.symm

/-- Transposing the same strict span grid twice restores all original objects and arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:62"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem transpose_transpose (G : SpanGrid.{u}) : G.transpose.transpose = G := rfl

variable (G : SpanGrid.{u})

/-- The original reduced homotopy pushout of one row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:67"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def row (i : Fin 3) : LoopPrespectrum.{u} :=
  prespectrum (G.horizontalLeft i) (G.horizontalRight i)

/-- The original map of row pushouts induced by the three left column arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:71"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def rowLeft : G.row 0 ⟶ G.row 1 :=
  map (G.horizontalLeft 0) (G.horizontalRight 0) (G.horizontalLeft 1) (G.horizontalRight 1)
    (G.verticalLeft 0) (G.verticalLeft 1) (G.verticalLeft 2) G.left_left G.left_right

/-- The original map of row pushouts induced by the three right column arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:76"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def rowRight : G.row 0 ⟶ G.row 2 :=
  map (G.horizontalLeft 0) (G.horizontalRight 0) (G.horizontalLeft 2) (G.horizontalRight 2)
    (G.verticalRight 0) (G.verticalRight 1) (G.verticalRight 2) G.right_left G.right_right

/-- Take the horizontal reduced pushouts first, followed by the vertical reduced pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:81"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def iterated : LoopPrespectrum.{u} := prespectrum G.rowLeft G.rowRight

/-- The left row enters the transposed iterated pushout by its literal column inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:84"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeLeft : G.row 1 ⟶ G.transpose.iterated :=
  map (G.horizontalLeft 1) (G.horizontalRight 1) G.transpose.rowLeft G.transpose.rowRight
    (inl (G.verticalLeft 0) (G.verticalRight 0))
    (inl (G.verticalLeft 1) (G.verticalRight 1))
    (inl (G.verticalLeft 2) (G.verticalRight 2))
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The right row enters the same transposed pushout by its literal column inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:93"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeRight : G.row 2 ⟶ G.transpose.iterated :=
  map (G.horizontalLeft 2) (G.horizontalRight 2) G.transpose.rowLeft G.transpose.rowRight
    (inr (G.verticalLeft 0) (G.verticalRight 0))
    (inr (G.verticalLeft 1) (G.verticalRight 1))
    (inr (G.verticalLeft 2) (G.verticalRight 2))
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The whole left-column cylinder after inclusion into the transposed outer pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:102"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeLeftTrack : Homotopy
    (G.verticalLeft 1 ≫ inl (G.verticalLeft 1) (G.verticalRight 1) ≫
      inl G.transpose.rowLeft G.transpose.rowRight)
    (G.verticalRight 1 ≫ inr (G.verticalLeft 1) (G.verticalRight 1) ≫
      inl G.transpose.rowLeft G.transpose.rowRight) :=
  ((glue (G.verticalLeft 1) (G.verticalRight 1)).postcomp
    (inl G.transpose.rowLeft G.transpose.rowRight)).cast (by rfl) (by rfl)

/-- The whole right-column cylinder after inclusion into the transposed outer pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:111"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeRightTrack : Homotopy
    (G.verticalLeft 2 ≫ inl (G.verticalLeft 2) (G.verticalRight 2) ≫
      inr G.transpose.rowLeft G.transpose.rowRight)
    (G.verticalRight 2 ≫ inr (G.verticalLeft 2) (G.verticalRight 2) ≫
      inr G.transpose.rowLeft G.transpose.rowRight) :=
  ((glue (G.verticalLeft 2) (G.verticalRight 2)).postcomp
    (inr G.transpose.rowLeft G.transpose.rowRight)).cast (by rfl) (by rfl)

/-- The initial row cylinder transported through the actual left row map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:120"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeInitialTrack : Homotopy
    (G.horizontalLeft 0 ≫ G.verticalLeft 1 ≫
      inl (G.verticalLeft 1) (G.verticalRight 1) ≫
      inl G.transpose.rowLeft G.transpose.rowRight)
    (G.horizontalRight 0 ≫ G.verticalLeft 2 ≫
      inl (G.verticalLeft 2) (G.verticalRight 2) ≫
      inr G.transpose.rowLeft G.transpose.rowRight) :=
  ((glue (G.horizontalLeft 0) (G.horizontalRight 0)).postcomp
    (G.rowLeft ≫ G.interchangeLeft)).cast
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The final row cylinder transported through the actual right row map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:133"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeFinalTrack : Homotopy
    (G.horizontalLeft 0 ≫ G.verticalRight 1 ≫
      inr (G.verticalLeft 1) (G.verticalRight 1) ≫
      inl G.transpose.rowLeft G.transpose.rowRight)
    (G.horizontalRight 0 ≫ G.verticalRight 2 ≫
      inr (G.verticalLeft 2) (G.verticalRight 2) ≫
      inr G.transpose.rowLeft G.transpose.rowRight) :=
  ((glue (G.horizontalLeft 0) (G.horizontalRight 0)).postcomp
    (G.rowRight ≫ G.interchangeRight)).cast
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- Two original overlap cylinders form the full square with all four specified edges. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:146"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeSquare :
    G.interchangeInitialTrack.Square G.interchangeFinalTrack
      (Homotopy.precomp (G.horizontalLeft 0) G.interchangeLeftTrack)
      (Homotopy.precomp (G.horizontalRight 0) G.interchangeRightTrack) where
  level n := ⟨fun z ↦ cylinder G.transpose.rowLeft G.transpose.rowRight n
    (z.2.1, cylinder (G.verticalLeft 0) (G.verticalRight 0) n (z.1, z.2.2)), by fun_prop⟩
  at_zero n s x := by
    change cylinder G.transpose.rowLeft G.transpose.rowRight n
      (s, cylinder (G.verticalLeft 0) (G.verticalRight 0) n (0, x)) = _
    rw [cylinder_zero]
    rfl
  at_one n s x := by
    change cylinder G.transpose.rowLeft G.transpose.rowRight n
      (s, cylinder (G.verticalLeft 0) (G.verticalRight 0) n (1, x)) = _
    rw [cylinder_one]
    rfl
  left n r x := by
    change cylinder G.transpose.rowLeft G.transpose.rowRight n
      (0, cylinder (G.verticalLeft 0) (G.verticalRight 0) n (r, x)) = _
    rw [cylinder_zero]
    rfl
  right n r x := by
    change cylinder G.transpose.rowLeft G.transpose.rowRight n
      (1, cylinder (G.verticalLeft 0) (G.verticalRight 0) n (r, x)) = _
    rw [cylinder_one]
    rfl
  at_point n r s := by
    change cylinder G.transpose.rowLeft G.transpose.rowRight n
      (s, cylinder (G.verticalLeft 0) (G.verticalRight 0) n (r, (G.obj 0 0).point n)) = _
    rw [cylinder_point]
    exact cylinder_point G.transpose.rowLeft G.transpose.rowRight n s
  comm _n _r _s _x _t := rfl

/-- Descend the complete moving square before evaluating the outer overlap time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:180"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchangeTrack : Homotopy (G.rowLeft ≫ G.interchangeLeft)
    (G.rowRight ≫ G.interchangeRight) :=
  (descSquareHomotopy (G.horizontalLeft 0) (G.horizontalRight 0)
    G.interchangeLeftTrack G.interchangeRightTrack G.interchangeSquare).cast
    (by
      apply hom_ext
      · apply Hom.ext; funext n; ext x; rfl
      · apply Hom.ext; funext n; ext x; rfl
      · intro n s x; rfl)
    (by
      apply hom_ext
      · apply Hom.ext; funext n; ext x; rfl
      · apply Hom.ext; funext n; ext x; rfl
      · intro n s x; rfl)

/-- The actual coordinate interchange of the two original reduced homotopy pushouts. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:196"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
def interchange : G.iterated ⟶ G.transpose.iterated :=
  desc G.rowLeft G.rowRight G.interchangeLeft G.interchangeRight G.interchangeTrack

/-- The original left/left stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:200"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_left_left (n : ℕ) (x : (G.obj 1 1).space n) :
    G.interchange.map n
      (left G.rowLeft G.rowRight n (left (G.horizontalLeft 1) (G.horizontalRight 1) n x)) =
        left G.transpose.rowLeft G.transpose.rowRight n (left (G.verticalLeft 1)
          (G.verticalRight 1) n x) := rfl

/-- The original left/right stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:207"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_left_right (n : ℕ) (x : (G.obj 1 2).space n) :
    G.interchange.map n
      (left G.rowLeft G.rowRight n (right (G.horizontalLeft 1) (G.horizontalRight 1) n x)) =
        right G.transpose.rowLeft G.transpose.rowRight n (left (G.verticalLeft 2)
          (G.verticalRight 2) n x) := rfl

/-- The original left/cylinder stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:214"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_left_cylinder (n : ℕ) (s : unitInterval) (x : (G.obj 1 0).space n) :
    G.interchange.map n
      (left G.rowLeft G.rowRight n (cylinder (G.horizontalLeft 1) (G.horizontalRight 1) n (s, x))) =
        cylinder G.transpose.rowLeft G.transpose.rowRight n (s, left (G.verticalLeft 0)
          (G.verticalRight 0) n x) := rfl

/-- The original right/left stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:221"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_right_left (n : ℕ) (x : (G.obj 2 1).space n) :
    G.interchange.map n
      (right G.rowLeft G.rowRight n (left (G.horizontalLeft 2) (G.horizontalRight 2) n x)) =
        left G.transpose.rowLeft G.transpose.rowRight n (right (G.verticalLeft 1)
          (G.verticalRight 1) n x) := rfl

/-- The original right/right stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:228"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_right_right (n : ℕ) (x : (G.obj 2 2).space n) :
    G.interchange.map n
      (right G.rowLeft G.rowRight n (right (G.horizontalLeft 2) (G.horizontalRight 2) n x)) =
        right G.transpose.rowLeft G.transpose.rowRight n (right (G.verticalLeft 2)
          (G.verticalRight 2) n x) := rfl

/-- The original right/cylinder stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:235"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_right_cylinder (n : ℕ) (s : unitInterval) (x : (G.obj 2 0).space n) :
    G.interchange.map n
      (right G.rowLeft G.rowRight n (cylinder (G.horizontalLeft 2) (G.horizontalRight 2) n (s,
        x))) =
        cylinder G.transpose.rowLeft G.transpose.rowRight n (s, right (G.verticalLeft 0)
          (G.verticalRight 0) n x) := rfl

/-- The original cylinder/left stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:243"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_cylinder_left (n : ℕ) (r : unitInterval) (x : (G.obj 0 1).space n) :
    G.interchange.map n
      (cylinder G.rowLeft G.rowRight n (r, left (G.horizontalLeft 0) (G.horizontalRight 0) n x)) =
        left G.transpose.rowLeft G.transpose.rowRight n (cylinder (G.verticalLeft 1)
          (G.verticalRight 1) n (r, x)) := rfl

/-- The original cylinder/right stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:250"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_cylinder_right (n : ℕ) (r : unitInterval) (x : (G.obj 0 2).space n) :
    G.interchange.map n
      (cylinder G.rowLeft G.rowRight n (r, right (G.horizontalLeft 0) (G.horizontalRight 0) n x)) =
        right G.transpose.rowLeft G.transpose.rowRight n (cylinder (G.verticalLeft 2)
          (G.verticalRight 2) n (r, x)) := rfl

/-- The original cylinder/cylinder stratum keeps its point and every independent interval time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:257"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_cylinder_cylinder (n : ℕ) (r : unitInterval) (s : unitInterval) (x :
  (G.obj 0 0).space n) :
    G.interchange.map n
      (cylinder G.rowLeft G.rowRight n (r, cylinder (G.horizontalLeft 0) (G.horizontalRight 0) n
        (s, x))) =
        cylinder G.transpose.rowLeft G.transpose.rowRight n (s, cylinder (G.verticalLeft 0)
          (G.verticalRight 0) n (r, x)) := rfl

/-- The coordinate interchange is based on the original reduced quotient point. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:266"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata.", simp]
theorem interchange_point (n : ℕ) :
    G.interchange.map n (G.iterated.point n) = G.transpose.iterated.point n :=
  G.interchange.map_point n

/-- The original structure-loop time remains independent of both overlap coordinates. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutInterchange.lean:271"
  "adaptation" "Original actual two-pushout interchange on all nine quotient strata."]
theorem interchange_structure (n : ℕ) (x : G.iterated.space n) (t : unitInterval) :
    G.interchange.map (n + 1) (G.iterated.structureMap n x t) =
      G.transpose.iterated.structureMap n (G.interchange.map n x) t :=
  congrArg (fun p ↦ p t) (G.interchange.comm n x)

end SpanGrid
end Topology.LoopPrespectrum.HomotopyPushout
