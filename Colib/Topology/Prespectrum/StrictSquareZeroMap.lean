/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.StrictSquareCone

/-!
# Literal zero maps through the original reduced Bass square

The actual reduced pushout map of three zero side maps is the literal pointwise zero map:
its cylinder is collapsed by the original basepoint relation. The reduced cone has the same
property, so the unchanged parameter-looped cone functor sends an all-zero four-corner map
to literal zero. This is a proved map equality; it does not identify the value of the zero
square with an independently chosen point object. No homotopy or stable equivalence is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- The original reduced double-cylinder map collapses every generator for zero corner maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareZeroMap.lean:27-55"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem StrictSquare.spanMap_eq_zero
    (h00 : a.left.left = zeroHom S.left.left T.left.left)
    (h01 : a.left.right = zeroHom S.left.right T.left.right)
    (h10 : a.right.left = zeroHom S.right.left T.right.left) :
    StrictSquare.spanMap a = zeroHom (StrictSquare.span S) (StrictSquare.span T) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y =>
        change HomotopyPushout.left T.left.hom T.hom.left n (a.left.right.map n y) =
          HomotopyPushout.point T.left.hom T.hom.left n
        rw [h01]
        rfl
      | inr y =>
        change HomotopyPushout.right T.left.hom T.hom.left n (a.right.left.map n y) =
          HomotopyPushout.point T.left.hom T.hom.left n
        rw [h10]
        exact HomotopyPushout.right_point T.left.hom T.hom.left n
    | inr z =>
      change HomotopyPushout.cylinder T.left.hom T.hom.left n (z.1, a.left.left.map n z.2) =
        HomotopyPushout.point T.left.hom T.hom.left n
      rw [h00]
      exact HomotopyPushout.cylinder_point T.left.hom T.hom.left n z.1

/-- The actual cone and loop maps retain the literal zero endpoint of a zero square map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareZeroMap.lean:56-88"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem strictSquareLoopedConeFunctor_map_eq_zero
    (h00 : a.left.left = zeroHom S.left.left T.left.left)
    (h01 : a.left.right = zeroHom S.left.right T.left.right)
    (h10 : a.right.left = zeroHom S.right.left T.right.left)
    (h11 : a.right.right = zeroHom S.right.right T.right.right) :
    strictSquareLoopedConeFunctor.map a =
      zeroHom (strictSquareLoopedConeFunctor.obj S) (strictSquareLoopedConeFunctor.obj T) := by
  have hs := StrictSquare.spanMap_eq_zero a h00 h01 h10
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  change Path ((mappingCone (StrictSquare.comparison S)).point n)
    ((mappingCone (StrictSquare.comparison S)).point n) at γ
  apply Path.ext
  funext t
  change (mappingConeMap (strictSquareComparisonFunctor.map a)).map n (γ t) =
    (mappingCone (StrictSquare.comparison T)).point n
  induction γ t using Quot.inductionOn with
  | h z => cases z with
    | inl y =>
      change ReducedMappingCone.inr ((StrictSquare.span T).point n) (T.right.right.point n)
        ((StrictSquare.comparison T).map n) (a.right.right.map n y) = _
      rw [h11]
      rfl
    | inr z =>
      change ReducedMappingCone.cylinder ((StrictSquare.span T).point n) (T.right.right.point n)
        ((StrictSquare.comparison T).map n) (z.1, (StrictSquare.spanMap a).map n z.2) = _
      rw [hs]
      exact ReducedMappingCone.cylinder_base ((StrictSquare.span T).point n)
        (T.right.right.point n) ((StrictSquare.comparison T).map n) z.1

end Topology.LoopPrespectrum
