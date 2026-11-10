/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.FlatSourceTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle
public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental

/-!
# The actual flat-source incidence Tor cycle is its full fundamental cycle

Positive Tor vanishes by the constructed graph-list argument. The existing
ambient Tor-zero isomorphism retains the entire incidence stalk and the
surjective ambient scalar action, so its length is the true generic local
length. The actual finite integer Euler sum and actual pushforward are used.
The incidence need not be reduced, irreducible, or nonempty.

Source-only adaptation of motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Graph/Flat/LeftComposition.lean:197-220. No native acceptance is asserted.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

omit [Smooth f] [Smooth g] [IsSeparated g] [Smooth h] in
/-- Finite supports over a Noetherian source give a Noetherian whole incidence. -/
theorem isNoetherian_correspondenceIncidence_of_finite_source [IsNoetherian X]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsNoetherian (correspondenceIncidence f g h z w) := by
  have : IsFinite ((integralComponentAt z).subschemeι ≫ pullback.fst f g) := hz.1
  have : IsFinite ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := hw.1
  have : IsFinite (correspondenceIncidenceLeft f g h z w) := by
    dsimp only [correspondenceIncidenceLeft]
    infer_instance
  exact
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (correspondenceIncidenceLeft f g h z w)
      toCompactSpace :=
        QuasiCompact.compactSpace_of_compactSpace (correspondenceIncidenceLeft f g h z w) }

/-- The actual finite signed Euler sum is the full generic incidence length. -/
theorem correspondenceIncidenceTorCoefficient_eq_length_of_flat_source
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]
    (x : genericPoints (correspondenceIncidence f g h z w)) :
    correspondenceIncidenceTorCoefficient k f g h z w x =
      ((Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x.val)
        ((correspondenceIncidence f g h z w).presheaf.stalk x.val)).toNat : ℤ) := by
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f)
  have : IsLocallyNoetherian (integralComponentAt z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt z).subschemeι
  rw [correspondenceIncidenceTorCoefficient_eq_sum, Finset.sum_eq_single 0]
  · rw [length_correspondenceIncidenceAmbientTor_zero]
    simp
  · intro n hn hn0
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
      have hz := (Module.length_eq_zero_iff
        (R := correspondenceIncidenceAmbientStalk f g h z w x.val)).mpr
        (ModuleCat.isZero_iff_subsingleton.mp
          (isZero_correspondenceIncidenceTor_succ_of_flat_source f g h z w x.val n))
      simp only [hz, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

/-- The native Tor cycle equals the genuine whole incidence fundamental cycle. -/
theorem incidenceTorCycle_eq_fundamentalCycle_of_flat_source
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]
    [IsNoetherian (correspondenceIncidence f g h z w)]
    (hw : IsFiniteCorrespondencePoint g h w) :
    incidenceTorCycle f g h z w hw =
      AlgebraicCycle.fundamentalCycle (correspondenceIncidence f g h z w) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints (correspondenceIncidence f g h z w)
  · rw [incidenceTorCycle_apply_generic f g h z w hw ⟨x, hx⟩,
      AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨x, hx⟩]
    exact correspondenceIncidenceTorCoefficient_eq_length_of_flat_source f g h z w ⟨x, hx⟩
  · rw [incidenceTorCycle_apply_of_notMem f g h z w hw x hx,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem _ x hx]

/-- Actual finite pushforward retains every generic length and every residue degree. -/
theorem incidenceTorCorrespondence_val_of_flat_source [IsSeparated h]
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]
    [IsNoetherian (correspondenceIncidence f g h z w)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCorrespondence f g h z w hz hw).val =
      letI := isFinite_correspondenceIncidenceMap f g h z w hz hw
      finiteCyclePushforward (correspondenceIncidenceMap f g h z w)
        (AlgebraicCycle.fundamentalCycle (correspondenceIncidence f g h z w)) := by
  have := isFinite_correspondenceIncidenceMap f g h z w hz hw
  rw [incidenceTorCorrespondence_val, incidenceTorCycle_eq_fundamentalCycle_of_flat_source]

end Stacks.Chow
