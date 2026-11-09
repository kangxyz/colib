/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageGenericStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalMiddleList
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# A regular list at the actual original remaining Y diagonal

Smooth diagonal regularity supplies an ordered list at the original Y self-product
point of the actual right image incidence. The point lies on the actual diagonal
by its Cartesian square. No regularity, dimension or presentation is assumed.
This lower statement works over an arbitrary base with the displayed smoothness.
References: native regular immersion of a smooth section and the actual
regular-ideal stalk kernel supplier.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual smooth Y diagonal supplies the unchanged original ordered regular list. -/
theorem exists_correspondenceRightRemainingOriginalMiddleList [Smooth g] [IsSeparated g]
    (x : correspondenceRightImageIncidence f g h i z w v) :
    let m := correspondenceRightImageMiddlePair f g h i z w v
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)
    let A := (pullback g g).presheaf.stalk m
    ∃ (r : ℕ) (s : Fin r → A), IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker m = Ideal.span (Set.range s) := by
  dsimp only
  let m := correspondenceRightImageMiddlePair f g h i z w v
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)
  let y := (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)) x
  have hp : pullback.diagonal g y = m := by
    simpa only [y, Scheme.Hom.comp_apply] using
      congrArg (fun k => k x) (correspondenceRightImageMiddlePair_isPullback f g h i z w v).w.symm
  have hex : ∃ l : List ((pullback g g).presheaf.stalk (pullback.diagonal g y)),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g y)) l ∧
        IdealSheafData.stalk (pullback.diagonal g).ker (pullback.diagonal g y) =
          Ideal.ofList l := by
    obtain ⟨l, hl, hk⟩ :=
      Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
        (pullback.diagonal g)
        (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
          (pullback.fst g g) (pullback.diagonal g) (pullback.diagonal_fst g)) y
    exact ⟨l, hl, (ker_stalkMap_eq_idealStalk_ker (pullback.diagonal g) y).symm.trans hk.symm⟩
  rw [hp] at hex
  obtain ⟨l, hl, hk⟩ := hex
  refine ⟨l.length, l.get, ?_, ?_⟩
  · simpa only [List.ofFn_get] using hl
  · rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hk

end Stacks.Chow
