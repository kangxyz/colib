/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RowRefinement

/-!
# Actual maps preserving a specified row refinement

A whole spectrum map that commutes with the specified levelwise row interchanges acts on
the constructed row spectra. The original comparison square holds at every level, including
the explicit zero-level double structure. No commutation is inferred from stable classes.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (a : E ⟶ F)
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))

/-- The whole map on the distinguished rows, with its actual degree-zero loop extension. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementMap.lean:32-52"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def map : spectrum E qE hE ⟶ spectrum F qF hF where
  map n := Nat.casesOn n
    (basedLoopMap (basedLoopMap (a.map 2) (a.map_point 2)) (basedLoopMap_refl _ _))
    (fun k => basedLoopMap (a.map (k + 2)) (a.map_point (k + 2)))
  map_point n := by
    cases n <;> exact basedLoopMap_refl _ _
  comm n γ := by
    cases n with
    | zero => rfl
    | succ k =>
      change Path _ _ at γ
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      change a.map (k + 3) (qE k (E.structureMap (k + 2) (γ s) r)) =
        qF k (F.structureMap (k + 2) (a.map (k + 2) (γ s)) r)
      rw [← ha]
      exact congrArg (qF k) (congrArg (fun p => p r) (a.comm (k + 2) (γ s)))

/-- The positive map keeps the independent row coordinate unchanged. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementMap.lean:53-66"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem map_succ (k : ℕ) (γ : Path (E.point (k + 2)) (E.point (k + 2)))
    (s : unitInterval) :
    Path.toContinuousMap ((map qE qF hE hF a ha).map (k + 1) γ) s =
      a.map (k + 2) (γ s) := rfl

variable
  (hsE : ∀ k (x : E.space (k + 1)) (s t : unitInterval),
    qE k (E.structureMap (k + 2) (E.structureMap (k + 1) x s) t) =
      E.structureMap (k + 2) (E.structureMap (k + 1) x t) s)
  (hsF : ∀ k (x : F.space (k + 1)) (s t : unitInterval),
    qF k (F.structureMap (k + 2) (F.structureMap (k + 1) x s) t) =
      F.structureMap (k + 2) (F.structureMap (k + 1) x t) s)

/-- The two actual comparison maps commute strictly with the entire row map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementMap.lean:67-84"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem comparison_naturality :
    a ≫ comparison F qF hF hsF = comparison E qE hE hsE ≫ map qE qF hE hF a ha := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    change F.structureMap 1 (F.structureMap 0 (a.map 0 x) r) s =
      a.map 2 (E.structureMap 1 (E.structureMap 0 x r) s)
    rw [← congrArg (fun p => p r) (a.comm 0 x)]
    exact (congrArg (fun p => p s) (a.comm 1 (E.structureMap 0 x r))).symm
  | succ k => exact (a.comm (k + 1) x).symm

end Topology.LoopPrespectrum.RowRefinement
