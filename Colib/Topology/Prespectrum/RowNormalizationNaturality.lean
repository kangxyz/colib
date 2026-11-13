/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.RowNormalization
public import Colib.Topology.Prespectrum.RowNormalizedOperationNaturality
public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Whole input and target naturality of the prescribed row-normalization prism

An actual row-commuting target map and an actual source map preserve the whole normalization
prism whenever they preserve its original endpoint, self-track and specified null. Positive
levels use the existing parameterized prism. Degree zero uses the original source-map structure
square, retaining its independent loop parameter. The hypotheses concern only the three local
input data; no compatibility of the desired normalized prism is assumed.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {D D' E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (a : E ⟶ F)
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
  (b : D ⟶ D') (f : D ⟶ spectrum E qE hE) (f' : D' ⟶ spectrum F qF hF)
  (H : Homotopy f f) (H' : Homotopy f' f')
  (hf : f ≫ map qE qF hE hF a ha = b ≫ f')
  (hH : ∀ n t x, (map qE qF hE hF a ha).map n (H.level n (t, x)) =
    H'.level n (t, b.map n x))

include hf hH

/-- The original normalization preserves both actual endpoint and whole self-track squares. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowNormalizationNaturality.lean:46"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedStage_square (k : ℕ) (x : D.space (k + 1)) (t s : unitInterval) :
    a.map (k + 2) (normalizedStage qE hE f H k x t s) =
      normalizedStage qF hF f' H' k (b.map (k + 1) x) t s := by
  rw [normalizedStage_apply, normalizedStage_apply]
  apply loopNormalizedSelfTrack_pointwise (a.map (k + 2)) id
  · intro r
    exact congrArg (fun p : Path (F.point (k + 2)) (F.point (k + 2)) => p r)
      (congrArg (fun g : D ⟶ spectrum F qF hF => g.map (k + 1) x) hf)
  · intro r v
    exact congrArg (fun p : Path (F.point (k + 2)) (F.point (k + 2)) => p v)
      (hH (k + 1) r x)

/-- The complete normalized operations form the actual source/target naturality square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowNormalizationNaturality.lean:59"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedOperation_square :
    normalizedOperation qE hE f H ≫ parameterLoopingMap (map qE qF hE hF a ha) =
      b ≫ normalizedOperation qF hF f' H' := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    apply Path.ext
    funext t
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    exact (normalizedStage_square qE qF hE hF a ha b f f' H H' hf hH
      0 (D.structureMap 0 x r) t s).trans
      (congrArg (fun y => normalizedStage qF hF f' H' 0 y t s)
        (congrArg (fun p => p r) (b.comm 0 x)))
  | succ k =>
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact normalizedStage_square qE qF hE hF a ha b f f' H H' hf hH k x t s

variable (N : Homotopy f (zeroHom D (spectrum E qE hE)))
  (N' : Homotopy f' (zeroHom D' (spectrum F qF hF)))
  (hN : ∀ n t x, (map qE qF hE hF a ha).map n (N.level n (t, x)) =
    N'.level n (t, b.map n x))

include hN

/-- Every positive prism square retains its relative, unit and row times independently. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowNormalizationNaturality.lean:93"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizationStage_square (k : ℕ) (x : D.space (k + 1))
    (r t s : unitInterval) :
    a.map (k + 2) (normalizationStage qE hE f H N k (r, x) t s) =
      normalizationStage qF hF f' H' N' k (r, b.map (k + 1) x) t s := by
  apply LoopNormalizationPrism.normalizationHomotopy_pointwise (a.map (k + 2)) id
  · intro v
    exact congrArg (fun p : Path (F.point (k + 2)) (F.point (k + 2)) => p v)
      (congrArg (fun g : D ⟶ spectrum F qF hF => g.map (k + 1) x) hf)
  · intro v w
    exact congrArg (fun p : Path (F.point (k + 2)) (F.point (k + 2)) => p w)
      (hH (k + 1) v x)
  · intro v w
    exact congrArg (fun p : Path (F.point (k + 2)) (F.point (k + 2)) => p w)
      (hN (k + 1) v x)

/-- Whole continuous levels of the normalization prism commute with both actual input maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowNormalizationNaturality.lean:109"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizationHomotopy_square_level (n : ℕ) :
    ((normalizationHomotopy qE hE f H N).postcomp
      (parameterLoopingMap (map qE qF hE hF a ha))).level n =
    ((normalizationHomotopy qF hF f' H' N').precomp b).level n := by
  apply ContinuousMap.ext
  intro z
  cases n with
  | zero =>
    apply Path.ext
    funext t
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    change a.map 2 (normalizationStage qE hE f H N 0
      (z.1, D.structureMap 0 z.2 r) t s) =
        normalizationStage qF hF f' H' N' 0
          (z.1, D'.structureMap 0 (b.map 0 z.2) r) t s
    exact (normalizationStage_square qE qF hE hF a ha b f f' H H' hf hH N N' hN
      0 (D.structureMap 0 z.2 r) z.1 t s).trans
      (congrArg (fun y => normalizationStage qF hF f' H' N' 0 (z.1, y) t s)
        (congrArg (fun p => p r) (b.comm 0 z.2)))
  | succ k =>
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    change a.map (k + 2) (normalizationStage qE hE f H N k (z.1, z.2) t s) =
      normalizationStage qF hF f' H' N' k (z.1, b.map (k + 1) z.2) t s
    exact normalizationStage_square qE qF hE hF a ha b f f' H H' hf hH N N' hN k z.2 z.1 t s

omit hf in
/-- The same original null-conjugated endpoints form the complete naturality square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowNormalizationNaturality.lean:142"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizationNullLoop_square :
    H.nullLoopMap N ≫ parameterLoopingMap (map qE qF hE hF a ha) =
      b ≫ H'.nullLoopMap N' :=
  Homotopy.nullLoopMap_naturality b (map qE qF hE hF a ha) H H' N N'
    (fun n => ContinuousMap.ext (fun z => hH n z.1 z.2))
    (fun n => ContinuousMap.ext (fun z => hN n z.1 z.2))

/-- The complete structure-compatible normalization homotopies agree after their actual squares.
-/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowNormalizationNaturality.lean:151"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizationHomotopy_square :
    (((normalizationHomotopy qE hE f H N).postcomp
      (parameterLoopingMap (map qE qF hE hF a ha))).cast
        (normalizedOperation_square qE qF hE hF a ha b f f' H H' hf hH)
        (normalizationNullLoop_square qE qF hE hF a ha b f f' H H' hH N N' hN)) =
    (normalizationHomotopy qF hF f' H' N').precomp b := by
  apply Homotopy.ext
  funext n
  exact normalizationHomotopy_square_level qE qF hE hF a ha b f f' H H' hf hH N N' hN n

end Topology.LoopPrespectrum.RowRefinement
