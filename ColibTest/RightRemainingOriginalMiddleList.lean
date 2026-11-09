/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingOriginalMiddleList

/-! Literal endpoint consumers.  -/

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

example [Smooth g] [IsSeparated g]
    (x : correspondenceRightImageIncidence f g h i z w v) :
    let m := correspondenceRightImageMiddlePair f g h i z w v
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)
    let A := (pullback g g).presheaf.stalk m
    ∃ (r : ℕ) (s : Fin r → A), IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker m = Ideal.span (Set.range s)  := by
  exact exists_correspondenceRightRemainingOriginalMiddleList
    f g h i z w v x

end Stacks.Chow
