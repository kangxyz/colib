/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.StrictSquareMapHomotopy
public import Colib.Topology.Prespectrum.StrictSquareNull
public import Colib.Topology.Prespectrum.NullLoopNaturality

/-!
# Original source seeds under whole strict-square homotopies

The original source-leg cone null cylinder is natural at every time of a moving strict square.
If the two specified original scalar tracks commute with that same time slice, their original
null-conjugated seeds do as well. All moving-square, scalar, cone and output-loop parameters are
retained. The scalar interchange is an explicit input here and must be discharged for a concrete
Model transformation; no seed-relative compatibility is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.StrictSquare.MapHomotopy
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} {a b : S ⟶ T}
    (H : StrictSquare.MapHomotopy a b)

/-- Every moving-square time preserves the original source-leg null cylinder at its own time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareSeedHomotopy.lean:32-48"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem sourceNull_apply (n : ℕ) (r s : unitInterval) (x : S.left.left.space n) :
    H.cone.level n (r, (sourceNullHomotopy S).level n (s, x)) =
      (sourceNullHomotopy T).level n (s, H.source.level n (r, x)) := by
  have h := sourceNullHomotopy_naturality_apply (H.at r) n s x
  rw [← H.cone_at r] at h
  exact h

variable
    (U : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
    (V : Homotopy (T.left.hom ≫ T.hom.right) (T.left.hom ≫ T.hom.right))
    (hU : ∀ n r s x, H.target.level n (r, U.level n (s, x)) =
      V.level n (s, H.source.level n (r, x)))

include hU

/-- The original scalar track and original null cylinder give exact naturality of each seed
at every moving-square time, rather than only at its two endpoints. -/
@[colib_tag "COL-0516", colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareSeedHomotopy.lean:49-72"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem sourceSeed_at (r : unitInterval) :
    (U.postcomp (mappingConeInclusion (StrictSquare.comparison S))).nullLoopMap
        (sourceNullHomotopy S) ≫
        H.looped.at r =
      H.source.at r ≫
        (V.postcomp (mappingConeInclusion (StrictSquare.comparison T))).nullLoopMap
          (sourceNullHomotopy T) := by
  change _ ≫ H.cone.parameterLooping.at r = _
  rw [Homotopy.parameterLooping_at]
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change H.cone.level n
        (r, (mappingConeInclusion (StrictSquare.comparison S)).map n (U.level n (s, x))) =
      (mappingConeInclusion (StrictSquare.comparison T)).map n
        (V.level n (s, H.source.level n (r, x)))
    rw [H.cone_inclusion, hU]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact H.sourceNull_apply n r s x

/-- The entire unchanged based loop retains its original output-loop time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareSeedHomotopy.lean:73-83"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem sourceSeed_apply (n : ℕ) (r t : unitInterval) (x : S.left.left.space n) :
    Path.toContinuousMap
        (H.looped.level n (r,
          ((U.postcomp (mappingConeInclusion (StrictSquare.comparison S))).nullLoopMap
            (sourceNullHomotopy S)).map n x)) t =
      Path.toContinuousMap
        (((V.postcomp (mappingConeInclusion (StrictSquare.comparison T))).nullLoopMap
          (sourceNullHomotopy T)).map n (H.source.level n (r, x))) t :=
  congrArg (fun f => Path.toContinuousMap (f.map n x) t) (H.sourceSeed_at U V hU r)

end Topology.LoopPrespectrum.StrictSquare.MapHomotopy
