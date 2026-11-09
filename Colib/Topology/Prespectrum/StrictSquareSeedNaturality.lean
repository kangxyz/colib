/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.StrictSquareNull
public import Colib.Topology.Prespectrum.NullLoopNaturality

/-!
# Original null-conjugated seeds under a strict square map

A map of strict squares preserves the original source-null cylinder. If it also
preserves the specified scalar self-track at every time, it preserves the whole
original null/unit/null seed. The target is the original looped cone map of this
square map. The local same-time scalar equation is an explicit generic input;
concrete geometric applications must prove it for their original units.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StrictSquareSeedNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (e : S ⟶ T)
    (U : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
    (V : Homotopy (T.left.hom ≫ T.hom.right) (T.left.hom ≫ T.hom.right))
    (hU : ∀ n r x, e.right.right.map n (U.level n (r, x)) =
      V.level n (r, e.left.left.map n x))

include hU in
/-- The exact original null/unit/null word is natural under the given strict square map. -/
theorem sourceSeed_naturality :
    (U.postcomp (mappingConeInclusion (comparison S))).nullLoopMap
        (sourceNullHomotopy S) ≫ strictSquareLoopedConeFunctor.map e =
      e.left.left ≫ (V.postcomp (mappingConeInclusion (comparison T))).nullLoopMap
        (sourceNullHomotopy T) := by
  change _ ≫ parameterLoopingMap (mappingConeMap (strictSquareComparisonFunctor.map e)) = _
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact congrArg ((mappingConeInclusion (comparison T)).map n) (hU n r x)
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact sourceNullHomotopy_naturality_apply e n r x

include hU in
/-- Every original output-loop coordinate is retained, independently of the scalar-track time. -/
theorem sourceSeed_naturality_apply (n : ℕ) (t : unitInterval) (x : S.left.left.space n) :
    Path.toContinuousMap
      ((strictSquareLoopedConeFunctor.map e).map n
        (((U.postcomp (mappingConeInclusion (comparison S))).nullLoopMap
          (sourceNullHomotopy S)).map n x)) t =
    Path.toContinuousMap
      (((V.postcomp (mappingConeInclusion (comparison T))).nullLoopMap
        (sourceNullHomotopy T)).map n (e.left.left.map n x)) t :=
  congrArg (fun f => Path.toContinuousMap (f.map n x) t) (sourceSeed_naturality e U V hU)

end Topology.LoopPrespectrum.StrictSquare

attribute [colib_tag "COL-0338",
  colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareSeedNaturality.lean" "adaptation"
    "Actual strict-square cylinder, cone-loop maps and supplied-seed finite iteration"]
  Topology.LoopPrespectrum.StrictSquare.sourceSeed_naturality
  Topology.LoopPrespectrum.StrictSquare.sourceSeed_naturality_apply
