/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Homotopy.Path

/-!
# Retype a whole unit comparison along its two given whole movement rails

Adapted from Quillen's `Aglib/Topology/Path/RetypedUnitComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

For paths in any topological space, the two stated whole-rail pointwise equalities retype the
endpoints of a given unit comparison. The selected homotopy and both interior times remain
unchanged.


-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.RetypedUnitComparison
variable {X : Type u} [TopologicalSpace X] {a b c d a' b' c' d' : X}
  (U : Path a a') (V : Path b b') (L : Path a b) (M : Path a' b')
  (L' : Path c d) (M' : Path c' d')
  (hL : ∀ s, L s = L' s) (hM : ∀ s, M s = M' s)

/-- The lower source equality follows from the entire lower rail. -/
theorem lower_source (L : Path a b) (L' : Path c d)
    (hL : ∀ s, L s = L' s) : c = a :=
  (L'.source).symm.trans ((hL 0).symm.trans (L.source))
/-- The lower target equality follows from the entire lower rail. -/
theorem lower_target (L : Path a b) (L' : Path c d)
    (hL : ∀ s, L s = L' s) : d = b :=
  (L'.target).symm.trans ((hL 1).symm.trans (L.target))
/-- The upper source equality follows from the entire upper rail. -/
theorem upper_source (M : Path a' b') (M' : Path c' d')
    (hM : ∀ s, M s = M' s) : c' = a' :=
  (M'.source).symm.trans ((hM 0).symm.trans (M.source))
/-- The upper target equality follows from the entire upper rail. -/
theorem upper_target (M : Path a' b') (M' : Path c' d')
    (hM : ∀ s, M s = M' s) : d' = b' :=
  (M'.target).symm.trans ((hM 1).symm.trans (M.target))

/-- The old unit retains its function and acquires the selected movement sources. -/
def oldUnit : Path c c' := U.cast (lower_source L L' hL) (upper_source M M' hM)
/-- The new unit retains its function and acquires the selected movement targets. -/
def newUnit : Path d d' := V.cast (lower_target L L' hL) (upper_target M M' hM)

/-- Endpoint replacement leaves every old-unit value unchanged. -/
theorem oldUnit_apply (s : I) : oldUnit U L M L' M' hL hM s = U s := rfl
/-- Endpoint replacement leaves every new-unit value unchanged. -/
theorem newUnit_apply (s : I) : newUnit V L M L' M' hL hM s = V s := rfl

/-- The full original comparison with exactly the selected whole movement rails. -/
def comparison (J : (U.trans M).Homotopy (L.trans V)) :
    ((oldUnit U L M L' M' hL hM).trans M').Homotopy
      (L'.trans (newUnit V L M L' M' hL hM)) := by
  refine (J.pathCast (lower_source L L' hL) (upper_target M M' hM)).cast ?_ ?_
  · apply Path.ext
    funext s
    change (U.trans M) s = ((oldUnit U L M L' M' hL hM).trans M') s
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · rfl
    · exact hM _
  · apply Path.ext
    funext s
    change (L.trans V) s = (L'.trans (newUnit V L M L' M' hL hM)) s
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hL _
    · rfl

/-- All comparison and path times survive the endpoint replacement literally. -/
theorem comparison_apply (J : (U.trans M).Homotopy (L.trans V)) (r s : I) :
    comparison U V L M L' M' hL hM J (r, s) = J (r, s) := rfl

end Path.RetypedUnitComparison
