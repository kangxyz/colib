/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.StrictSquareCone

/-!
# The original source nullhomotopy of a strict square

The source corner maps into the original double mapping cylinder along its left leg.
Precomposing the original mapping-cone contraction with this exact map nullhomotopes the
source-to-final-corner composite. Every interval point, and the entire coherent homotopy,
is natural under strict maps of squares with the original quotient-cone maps.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StrictSquareNull.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare

variable (S : Arrow (Arrow LoopPrespectrum.{u}))

/-- The original source corner enters the double cylinder along its left source leg. -/
def sourceLeg : S.left.left ⟶ span S :=
  S.left.hom ≫ HomotopyPushout.inl S.left.hom S.hom.left

/-- The actual comparison recovers the original source-to-final-corner composite. -/
@[simp] theorem sourceLeg_comparison :
    sourceLeg S ≫ comparison S = S.left.hom ≫ S.hom.right := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- Restrict the original cone contraction to the literal source leg. -/
def sourceNullHomotopy :
    Homotopy ((S.left.hom ≫ S.hom.right) ≫ mappingConeInclusion (comparison S))
      (zeroHom S.left.left (mappingCone (comparison S))) :=
  ((mappingConeHomotopy (comparison S)).precomp (sourceLeg S)).cast
    (by rw [← Category.assoc, sourceLeg_comparison])
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The nullhomotopy retains the original cone coordinate and exact source-leg point. -/
@[simp] theorem sourceNullHomotopy_apply (n : ℕ) (s : unitInterval) (x : S.left.left.space n) :
    (sourceNullHomotopy S).level n (s, x) =
      ReducedMappingCone.cylinder ((span S).point n) (S.right.right.point n)
        ((comparison S).map n) (s, (sourceLeg S).map n x) := rfl

variable {S T : Arrow (Arrow LoopPrespectrum.{u})}

/-- A strict map of squares preserves the actual source leg into the double cylinder. -/
theorem sourceLeg_naturality (a : S ⟶ T) :
    sourceLeg S ≫ spanMap a = a.left.left ≫ sourceLeg T := by
  apply Hom.ext
  funext n
  ext x
  exact congrArg (HomotopyPushout.left T.left.hom T.hom.left n)
    (congrArg (fun h ↦ h.map n x) a.left.w.symm)

/-- Every original cone interval point is strictly natural under the coefficient map. -/
theorem sourceNullHomotopy_naturality_apply (a : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : S.left.left.space n) :
    (mappingConeMap (strictSquareComparisonFunctor.map a)).map n
        ((sourceNullHomotopy S).level n (s, x)) =
      (sourceNullHomotopy T).level n (s, a.left.left.map n x) := by
  change ReducedMappingCone.cylinder ((span T).point n) (T.right.right.point n)
      ((comparison T).map n) (s, (sourceLeg S ≫ spanMap a).map n x) =
    ReducedMappingCone.cylinder ((span T).point n) (T.right.right.point n)
      ((comparison T).map n) (s, (a.left.left ≫ sourceLeg T).map n x)
  rw [sourceLeg_naturality]

/-- The starting arrows of the original nullhomotopies satisfy their strict square. -/
theorem sourceNullHomotopy_start_naturality (a : S ⟶ T) :
    ((S.left.hom ≫ S.hom.right) ≫ mappingConeInclusion (comparison S)) ≫
        mappingConeMap (strictSquareComparisonFunctor.map a) =
      a.left.left ≫ ((T.left.hom ≫ T.hom.right) ≫ mappingConeInclusion (comparison T)) := by
  apply Hom.ext
  funext n
  ext x
  have h := sourceNullHomotopy_naturality_apply a n 0 x
  rw [(sourceNullHomotopy S).at_zero, (sourceNullHomotopy T).at_zero] at h
  exact h

/-- The terminal zero arrows retain the exact source and target coefficient maps. -/
theorem sourceNullHomotopy_end_naturality (a : S ⟶ T) :
    zeroHom S.left.left (mappingCone (comparison S)) ≫
        mappingConeMap (strictSquareComparisonFunctor.map a) =
      a.left.left ≫ zeroHom T.left.left (mappingCone (comparison T)) := by
  apply Hom.ext
  funext n
  ext x
  exact (mappingConeMap (strictSquareComparisonFunctor.map a)).map_point n

/-- Naturality is equality of whole coherent homotopies after explicit endpoint transport. -/
theorem sourceNullHomotopy_naturality (a : S ⟶ T) :
    ((sourceNullHomotopy S).postcomp
        (mappingConeMap (strictSquareComparisonFunctor.map a))).cast
        (sourceNullHomotopy_start_naturality a) (sourceNullHomotopy_end_naturality a) =
      (sourceNullHomotopy T).precomp a.left.left := by
  apply Homotopy.ext
  funext n
  ext z
  exact sourceNullHomotopy_naturality_apply a n z.1 z.2

end Topology.LoopPrespectrum.StrictSquare

attribute [colib_tag "COL-0338",
  colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareNull.lean" "adaptation"
    "Actual strict-square cylinder, cone-loop maps and supplied-seed finite iteration"]
  Topology.LoopPrespectrum.StrictSquare.sourceNullHomotopy
  Topology.LoopPrespectrum.StrictSquare.sourceNullHomotopy_naturality
