/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductSpatial
public import Colib.Topology.Homotopy.SquareEdges

public import Colib.Util.References

/-! # Whole unit and supplied-null coherence of compact coproduct separation

Both squares are the displayed continuous families. Their boundary comparison is the original
explicit square interpolation. The original supplied null path and all spatial boundaries remain
present, including input degree one; no group-class additivity supplies a path.
-/
/-! Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original universes, canonical maps,
coordinates and boundaries are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology SSet
open CategoryTheory.Waldhausen.Product
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C] (n : ℕ)

private theorem leftUnit_delay_right
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (s t : unitInterval) :
    coproductLeftUnitCubeMap W n (s, genLoopDelayRight n (t, q)) =
      genLoopDelayRight n (t, coproductLeftUnitCubeMap W n (s, q)) := by
  ext z
  rfl

private theorem leftUnit_trans_const
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (s : unitInterval) :
    coproductLeftUnitCubeMap W n (s, GenLoop.transAt 0 q GenLoop.const) =
      GenLoop.transAt 0 (coproductLeftUnitCubeMap W n (s, q)) GenLoop.const := by
  have h := leftUnit_delay_right W n q s 0
  rw [genLoopDelayRight_zero, genLoopDelayRight_zero] at h
  exact h

/-- The actual zero-left unitor is evaluated on the complete reversed suffix-removal path. -/
def coproductUnitCoherenceSquare
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) where
  toFun z := coproductLeftUnitCubeMap W n (z.2, genLoopDelayRight n (σ z.1, q))
  continuous_toFun := (coproductLeftUnitCubeMap W n).continuous.comp
    (continuous_snd.prodMk ((genLoopDelayRight n).continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_const)))

/-- The square retains both actual parameters without further reparametrization. -/
theorem coproductUnitCoherenceSquare_apply
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (s t : unitInterval) :
    coproductUnitCoherenceSquare W n q (s, t) =
      coproductLeftUnitCubeMap W n (t, genLoopRightUnitPath n q (σ s)) := rfl

/-- The zero-left separation path is the actual unitor followed by reversed suffix removal. -/
def coproductSeparationZeroLeftHomotopy
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    (coproductSeparationPath n W GenLoop.const q).Homotopy
      ((coproductLeftUnitPath W n q).trans (genLoopRightUnitPath n q).symm) := by
  have H := Topology.squareEdgeHomotopy (coproductLeftUnitPath W n q)
    (genLoopRightUnitPath n q).symm
    (coproductSeparationDelayPath n W GenLoop.const q)
    (coproductSeparationUnitPath n W GenLoop.const q)
    (coproductUnitCoherenceSquare W n q)
    (fun t ↦ by
      change coproductLeftUnitCubeMap W n (t, genLoopDelayRight n (σ 0, q)) = _
      rw [unitInterval.symm_zero, genLoopDelayRight_one]
      rfl)
    (fun t ↦ by
      exact (coproductLeftUnitPath W n (genLoopDelayRight n (σ t, q))).target)
    (fun t ↦ by
      change coproductLeftUnitCubeMap W n (0, genLoopDelayRight n (σ t, q)) =
        coproductCube W n (genLoopDelayLeft n (σ t, GenLoop.const))
          (genLoopDelayRight n (σ t, q))
      rw [genLoopDelayLeft_const]
      exact (coproductLeftUnitPath W n (genLoopDelayRight n (σ t, q))).source)
    (fun t ↦ by
      change coproductLeftUnitCubeMap W n (t, genLoopDelayRight n (σ 1, q)) =
        GenLoop.transAt 0 (coproductLeftUnitCubeMap W n (t, q))
          (coproductRightUnitPath W n GenLoop.const t)
      rw [unitInterval.symm_one, genLoopDelayRight_zero,
        coproductRightUnitPath_const, leftUnit_trans_const])
  exact H.symm.cast (coproductSeparationPath_eq n W GenLoop.const q).symm rfl

/-- Actual suffix cancellation gives the complete zero-left unit coherence. -/
def coproductSeparationUnitCoherence
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    ((coproductSeparationPath n W GenLoop.const q).trans
      (genLoopRightUnitPath n q)).Homotopy (coproductLeftUnitPath W n q) :=
  ((coproductSeparationZeroLeftHomotopy W n q).hcomp
    (Path.Homotopy.refl (genLoopRightUnitPath n q))).trans
      ((Path.Homotopy.transAssoc (coproductLeftUnitPath W n q)
        (genLoopRightUnitPath n q).symm (genLoopRightUnitPath n q)).trans
          (((Path.Homotopy.refl (coproductLeftUnitPath W n q)).hcomp
            (Path.Homotopy.reflSymmTrans (genLoopRightUnitPath n q)).symm).trans
              (Path.Homotopy.transRefl (coproductLeftUnitPath W n q))))

omit [HasBinaryCoproducts C] in
/-- Left spatial concatenation retains the entire supplied original path. -/
def genLoopLeftConcatPath
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    {c d : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint} (N : Path c d) :
    Path (GenLoop.transAt 0 q c) (GenLoop.transAt 0 q d) :=
  ((Path.refl q).prod N).map (genLoopTransAtContinuousMap 0).continuous

/-- Both deformation times enter the actual compact separation before the square is transposed. -/
def coproductNullCoherenceSquare
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :=
  (coproductSeparationFamily n W N.toContinuousMap
    (ContinuousMap.const unitInterval q)).toContinuousMap.comp
      ⟨_root_.Prod.swap, continuous_swap⟩

/-- The full supplied null parameter remains separate from separation time. -/
theorem coproductNullCoherenceSquare_apply
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (s t : unitInterval) :
    coproductNullCoherenceSquare W n N q (s, t) = coproductSeparationPath n W (N s) q t :=
  coproductSeparationFamily_apply n W N.toContinuousMap (ContinuousMap.const unitInterval q) t s

/-- The actual supplied null path gives the whole unitor/separation coherence. -/
def coproductSeparationNullCoherence
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    ((coproductCubePath W n N (Path.refl q)).trans
      (coproductLeftUnitPath W n q)).Homotopy
        ((coproductSeparationPath n W c q).trans
          ((genLoopLeftConcatPath W n q N).trans (genLoopRightUnitPath n q))) := by
  have H := Topology.squareEdgeHomotopy (coproductSeparationPath n W c q)
    (genLoopLeftConcatPath W n q N) (coproductCubePath W n N (Path.refl q))
    (coproductSeparationPath n W GenLoop.const q) (coproductNullCoherenceSquare W n N q)
    (fun t ↦ by rw [coproductNullCoherenceSquare_apply, N.source])
    (fun t ↦ by
      rw [coproductNullCoherenceSquare_apply]
      exact (coproductSeparationPath n W (N t) q).target)
    (fun t ↦ by
      rw [coproductNullCoherenceSquare_apply]
      exact (coproductSeparationPath n W (N t) q).source)
    (fun t ↦ by rw [coproductNullCoherenceSquare_apply, N.target])
  exact ((Path.Homotopy.refl (coproductCubePath W n N (Path.refl q))).hcomp
    (coproductSeparationUnitCoherence W n q).symm).trans
      ((Path.Homotopy.transAssoc (coproductCubePath W n N (Path.refl q))
        (coproductSeparationPath n W GenLoop.const q) (genLoopRightUnitPath n q)).symm.trans
          ((H.symm.hcomp (Path.Homotopy.refl (genLoopRightUnitPath n q))).trans
            (Path.Homotopy.transAssoc (coproductSeparationPath n W c q)
              (genLoopLeftConcatPath W n q N) (genLoopRightUnitPath n q))))

/-- Every intermediate point of the whole null coherence keeps the original spatial boundary. -/
theorem coproductSeparationNullCoherence_boundary
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (s t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductSeparationNullCoherence W n N q (s, t) z = W.kBasepoint :=
  (coproductSeparationNullCoherence W n N q (s, t)).property z hz


attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean:73-79" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductUnitCoherenceSquare

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean:118-128" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationUnitCoherence

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean:139-145" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductNullCoherenceSquare

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean:156-180" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationNullCoherence

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean:183-189" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationNullCoherence_boundary

end CategoryTheory.Waldhausen.Additivity
