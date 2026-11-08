/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.SelfTrackStableOperation

/-! # Supplied relative comparisons preserve the actual self-track operations -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackRelativeHomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}

/-- A supplied whole relative comparison evaluates on the same original cube and both times. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackRelativeHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def Homotopy.RelHomotopy.genLoopPathHomotopy {H K : Homotopy f g}
    (J : H.RelHomotopy K) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    (H.genLoopPath n p).Homotopy (K.genLoopPath n p) where
  toFun rs := (J.at rs.1).genLoopPath n p rs.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × unitInterval) ×
      (Fin (m + 1) → unitInterval) ↦ (J.level n) (z.1.1, (z.1.2, p z.2)))
    fun_prop
  map_zero_left s := by
    ext z
    exact (J.level n).apply_zero (s, p z)
  map_one_left s := by
    ext z
    exact (J.level n).apply_one (s, p z)
  prop' r s hs := by
    ext z
    rcases Set.mem_insert_iff.mp hs with hs | hs
    · subst s
      exact (J.level n).eq_fst r (Or.inl rfl)
    · have hs := Set.mem_singleton_iff.mp hs
      subst s
      exact (J.level n).eq_fst r (Or.inr (Or.inl rfl))

/-- Neither the relative-comparison time nor the original track time is changed. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackRelativeHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem Homotopy.RelHomotopy.genLoopPathHomotopy_apply {H K : Homotopy f g}
    (J : H.RelHomotopy K) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n))
    (r s : unitInterval) (z : Fin (m + 1) → unitInterval) :
    J.genLoopPathHomotopy n m p (r, s) z = J.level n (r, (s, p z)) := rfl

/-- The supplied relative comparison identifies the finite operations on all original classes. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackRelativeHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.RelHomotopy.homotopyClassOperation_eq {H K : Homotopy f f}
    (J : H.RelHomotopy K) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.homotopyClassOperation n m a = K.homotopyClassOperation n m a := by
  induction a using Quotient.inductionOn with
  | h p =>
    exact (genLoopSelfTrackClass_eq_iff m _ _ _).mpr ⟨J.genLoopPathHomotopy n m p⟩

/-- The comparison retains the unchanged stable stages in every integer degree. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackRelativeHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.RelHomotopy.stableStageOperation_eq {H K : Homotopy f f}
    (J : H.RelHomotopy K) (d : ℤ) (n : ℕ) :
    H.stableStageOperation d n = K.stableStageOperation d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (J.homotopyClassOperation_eq ((-d).toNat + n + 2) (d.toNat + n + 1)
      (Additive.toMul a))

/-- A given whole relative comparison identifies the original colimit operations. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackRelativeHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.RelHomotopy.stableOperation_eq {H K : Homotopy f f}
    (J : H.RelHomotopy K) (d : ℤ) : H.stableOperation d = K.stableOperation d := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫ H.stableOperation d =
    stableHomotopyι E d n ≫ K.stableOperation d
  rw [H.stableOperation_ι, K.stableOperation_ι, J.stableStageOperation_eq]

end Topology.LoopPrespectrum
