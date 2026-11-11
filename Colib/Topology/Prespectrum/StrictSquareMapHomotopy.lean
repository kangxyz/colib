/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.PushoutMapHomotopy
public import Colib.Topology.Prespectrum.ConeMapHomotopy
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy
public import Colib.Topology.Prespectrum.StrictSquareCone

/-!
# Whole homotopies of the original strict Bass square maps

Four specified corner homotopies forming strict squares at every time induce a homotopy
of the existing reduced-span, cone and parameter-loop maps. The actual moving-boundary
pushout descent is followed by the original moving-cone and parameter-loop constructions.
Time slices are the original strict square maps; homotopy, overlap-cylinder, cone-cylinder,
loop and structure times remain independent. No seed-relative pasting is asserted here.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T : Arrow (Arrow LoopPrespectrum.{u})}

/-- A whole homotopy of strict square maps, with the four original all-time edge equations. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:33-58"
  "adaptation" "Original whole maps and independent time coordinates retained"]
structure MapHomotopy (a b : S ⟶ T) where
  /-- The original overlap corner track. -/
  source : Homotopy a.left.left b.left.left
  /-- The original upper target track. -/
  upper : Homotopy a.left.right b.left.right
  /-- The original lower target track. -/
  lower : Homotopy a.right.left b.right.left
  /-- The original final corner track. -/
  target : Homotopy a.right.right b.right.right
  /-- The first source leg commutes at every time. -/
  commUpper : ∀ n r x, upper.level n (r, S.left.hom.map n x) =
    T.left.hom.map n (source.level n (r, x))
  /-- The second source leg commutes at every time. -/
  commLower : ∀ n r x, lower.level n (r, S.hom.left.map n x) =
    T.hom.left.map n (source.level n (r, x))
  /-- The final upper leg commutes at every time. -/
  commRight : ∀ n r x, target.level n (r, S.hom.right.map n x) =
    T.hom.right.map n (upper.level n (r, x))
  /-- The final lower leg commutes at every time. -/
  commBottom : ∀ n r x, target.level n (r, S.right.hom.map n x) =
    T.right.hom.map n (lower.level n (r, x))

namespace MapHomotopy
variable {a b : S ⟶ T} (H : MapHomotopy a b)

/-- Each actual time gives the original strict square formed by the four time slices. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:59-70"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def «at» (r : unitInterval) : S ⟶ T :=
  Arrow.homMk
    (Arrow.homMk (H.source.at r) (H.upper.at r) (by
      apply Hom.ext; funext n; ext x; exact (H.commUpper n r x).symm))
    (Arrow.homMk (H.lower.at r) (H.target.at r) (by
      apply Hom.ext; funext n; ext x; exact (H.commBottom n r x).symm))
    (by
      apply Arrow.hom_ext
      · apply Hom.ext; funext n; ext x; exact (H.commLower n r x).symm
      · apply Hom.ext; funext n; ext x; exact (H.commRight n r x).symm)

/-- The whole moving reduced-span map, using the original strict attaching squares. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:71-77"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def span : Homotopy (spanMap a) (spanMap b) :=
  HomotopyPushout.mapHomotopy S.left.hom S.hom.left T.left.hom T.hom.left
    a.left.w.symm (congrArg (fun f => f.left) a.w).symm
    b.left.w.symm (congrArg (fun f => f.left) b.w).symm
    H.source H.upper H.lower H.commUpper H.commLower

/-- A time slice is exactly the original strict map of reduced spans. -/
@[colib_tag "COL-0514", colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:78-88"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem span_at (r : unitInterval) : H.span.at r = spanMap (H.at r) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl

/-- The original constant-track comparisons commute with the entire moving span. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:89-101"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem comparison (n : ℕ) (r : unitInterval) (q : (StrictSquare.span S).space n) :
    H.target.level n (r, (StrictSquare.comparison S).map n q) =
      (StrictSquare.comparison T).map n (H.span.level n (r, q)) := by
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y => exact H.commRight n r y
      | inr y => exact H.commBottom n r y
    | inr z =>
      exact (H.commRight n r (S.left.hom.map n z.2)).trans
        (congrArg (T.hom.right.map n) (H.commUpper n r z.2))

/-- The same original comparison arrows induce the entire moving cone map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:102-106"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def cone : Homotopy (mappingConeMap (strictSquareComparisonFunctor.map a))
    (mappingConeMap (strictSquareComparisonFunctor.map b)) :=
  mappingConeMapHomotopy H.span H.target H.comparison

/-- Every cone-map time slice is the unchanged cone functor applied to the strict square slice. -/
@[colib_tag "COL-0514", colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:107-116"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem cone_at (r : unitInterval) :
    H.cone.at r = mappingConeMap (strictSquareComparisonFunctor.map (H.at r)) := by
  apply mappingCone_hom_ext (StrictSquare.comparison S)
  · apply Hom.ext; funext n; ext x; rfl
  · intro n s x
    exact congrArg (fun y => ReducedMappingCone.cylinder ((StrictSquare.span T).point n)
      (T.right.right.point n) ((StrictSquare.comparison T).map n) (s, y))
        (congrArg (fun f => f.map n x) (H.span_at r))

/-- Pointwise parameter looping yields the whole homotopy of the actual Bass square maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:117-120"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def looped : Homotopy (strictSquareLoopedConeFunctor.map a)
    (strictSquareLoopedConeFunctor.map b) := H.cone.parameterLooping

/-- Every actual Bass time slice is the original functor applied to the same strict square. -/
@[colib_tag "COL-0514", colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:121-127"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem looped_at (r : unitInterval) :
    H.looped.at r = strictSquareLoopedConeFunctor.map (H.at r) := by
  change H.cone.parameterLooping.at r = parameterLoopingMap _
  rw [Homotopy.parameterLooping_at, H.cone_at]
  rfl

/-- The entire original upper face retains the given moving upper corner. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:128-132"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem span_inl (n : ℕ) (r : unitInterval) (y : S.left.right.space n) :
    H.span.level n (r, (HomotopyPushout.inl S.left.hom S.hom.left).map n y) =
      (HomotopyPushout.inl T.left.hom T.hom.left).map n (H.upper.level n (r, y)) := rfl

/-- The original overlap height remains independent of the moving-corner time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:133-137"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem span_cylinder (n : ℕ) (r q : unitInterval) (x : S.left.left.space n) :
    H.span.level n (r, HomotopyPushout.cylinder S.left.hom S.hom.left n (q, x)) =
      HomotopyPushout.cylinder T.left.hom T.hom.left n (q, H.source.level n (r, x)) := rfl

/-- The original Laurent target face is the given final-corner track followed by inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:138-142"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem cone_inclusion (n : ℕ) (r : unitInterval) (y : S.right.right.space n) :
    H.cone.level n (r, (mappingConeInclusion (StrictSquare.comparison S)).map n y) =
      (mappingConeInclusion (StrictSquare.comparison T)).map n (H.target.level n (r, y)) := rfl

/-- Moving the span point preserves the original cone height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:143-149"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem cone_cylinder (n : ℕ) (r s : unitInterval) (z : (StrictSquare.span S).space n) :
    H.cone.level n (r, ReducedMappingCone.cylinder ((StrictSquare.span S).point n)
      (S.right.right.point n) ((StrictSquare.comparison S).map n) (s, z)) =
    ReducedMappingCone.cylinder ((StrictSquare.span T).point n) (T.right.right.point n)
      ((StrictSquare.comparison T).map n) (s, H.span.level n (r, z)) := rfl

/-- Homotopy and output-loop coordinates retain their independent original order. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareMapHomotopy.lean:150-156"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem looped_apply (n : ℕ) (r t : unitInterval)
    (γ : Path ((mappingCone (StrictSquare.comparison S)).point n)
      ((mappingCone (StrictSquare.comparison S)).point n)) :
    Path.toContinuousMap (H.looped.level n (r, γ)) t = H.cone.level n (r, γ t) := rfl

end MapHomotopy
end Topology.LoopPrespectrum.StrictSquare
