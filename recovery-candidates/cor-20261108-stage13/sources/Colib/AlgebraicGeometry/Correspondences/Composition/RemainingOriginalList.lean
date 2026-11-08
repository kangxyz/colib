/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleFirstStageAction
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingGenericStalk

/-!
# The original remaining list generates the actual remaining stalk kernel

The original second-diagonal ideal in the sixfold ambient is mapped through the
actual first-stage stalk map. Native Cartesian stalk-kernel base change identifies
its image with the full remaining-incidence kernel, without taking a radical.
Consequently the literal image of the original second list generates an ideal of
definition at an actual generic triple-incidence point. No finite-colength or
ideal-of-definition hypothesis is supplied by a caller.

The only base-change supplier is the pinned native
`Stacks.Flatness.ker_stalkMap_of_isPullback`. The private transport calculation
merely rewrites an ideal stalk along equality of its actual ambient points.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

private theorem map_idealStalk_stalkCongr {X : Scheme.{u}} (I : X.IdealSheafData)
    {x y : X} (h : x = y) :
    (IdealSheafData.stalk I x).map
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom = IdealSheafData.stalk I y := by
  subst h
  simp [TopCat.Presheaf.stalkCongr]

private theorem ker_stalkMap_eq_map_transported_idealStalk
    {X X' S S' : Scheme.{u}} {iX : X ⟶ X'} {gX : X ⟶ S}
    {gX' : X' ⟶ S'} {iS : S ⟶ S'} [IsClosedImmersion iS]
    (H : IsPullback iX gX gX' iS) (x : X) (p : S') (hp : p = gX' (iX x)) :
    RingHom.ker (iX.stalkMap x).hom =
      (IdealSheafData.stalk iS.ker p).map
        ((S'.presheaf.stalkCongr (Inseparable.of_eq hp)).hom ≫
          gX'.stalkMap (iX x)).hom := by
  subst p
  have hpt : iS (gX x) = gX' (iX x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m x) H.w.symm
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback H x hpt
  rw [ker_stalkMap_eq_idealStalk_ker iS (gX x), CommRingCat.hom_comp,
    ← Ideal.map_map, map_idealStalk_stalkCongr] at hk
  simpa [TopCat.Presheaf.stalkCongr] using hk

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The full remaining intersection is the actual pullback of the original
second ambient diagonal along the full first-stage exterior inclusion. -/
theorem correspondenceRemaining_secondAmbient_isPullback :
    IsPullback (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v)
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v ≫
        correspondenceFourfoldToSecondAmbient f g h i)
      (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
      (correspondenceSecondAmbientInclusion f g h i) :=
  ((correspondenceTripleIncidence_firstDiagonal_isPullback f g h i z w v).paste_horiz
    (correspondenceFourfold_diagonals_isPullback f g h i).flip).flip

/-- The remaining ideal is the image of the original second-diagonal ideal
under the genuine sixfold-to-first-stage stalk map, preserving nilpotents. -/
theorem correspondenceRemainingOriginalStalkIdeal_eq_map [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceRemainingOriginalStalkIdeal f g h i z w v x =
      (IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x)).map
          (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x) :=
  ker_stalkMap_eq_map_transported_idealStalk
    (correspondenceRemaining_secondAmbient_isPullback f g h i z w v) x _
    (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v x)

/-- The same original ambient second list, rather than new lifts, generates
the actual remaining kernel after the original first-stage stalk map. -/
theorem correspondenceRemainingOriginalStalkIdeal_eq_ofList [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hs : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList s) :
    correspondenceRemainingOriginalStalkIdeal f g h i z w v x =
      Ideal.ofList (s.map (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x)) := by
  rw [correspondenceRemainingOriginalStalkIdeal_eq_map, hs, Ideal.map_ofList]

/-- At each actual generic remaining intersection, the literal image of the
original second list is an ideal of definition. This is proved from geometry. -/
theorem isIdealOfDefinition_correspondenceRemainingOriginalList [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (hs : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList s) :
    IsIdealOfDefinition (Ideal.span (Set.range
      (s.map (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1)).get)) := by
  rw [← Ideal.ofList_ofFn, List.ofFn_get,
    ← correspondenceRemainingOriginalStalkIdeal_eq_ofList f g h i z w v x.1 s hs]
  exact isIdealOfDefinition_correspondenceRemainingOriginalStalkIdeal f g h i z w v x

end Stacks.Chow
