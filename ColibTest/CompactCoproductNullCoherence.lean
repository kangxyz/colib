/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductNullCoherence
public import ColibTest.CompactCoproductSpatial

/-! # Whole original unit and supplied-null path coherence -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity
open scoped Topology unitInterval
universe u v
namespace ColibTest.CompactCoproductNullCoherence
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C] (n : ℕ)

/-- The unit square retains its literal old suffix-removal path at both independent times. -/
theorem original_unit_square
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (s t : unitInterval) :
    coproductUnitCoherenceSquare W n q (s, t) =
      coproductLeftUnitCubeMap W n (t, genLoopRightUnitPath n q (σ s)) :=
  coproductUnitCoherenceSquare_apply W n q s t

/-- The actual suffix cancels through a displayed homotopy to the original zero-left unitor. -/
def original_unit_coherence
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    ((coproductSeparationPath n W GenLoop.const q).trans
      (genLoopRightUnitPath n q)).Homotopy (coproductLeftUnitPath W n q) :=
  coproductSeparationUnitCoherence W n q

/-- The complete supplied null time survives the transposed separation square. -/
theorem original_null_square
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (s t : unitInterval) :
    coproductNullCoherenceSquare W n N q (s, t) = coproductSeparationPath n W (N s) q t :=
  coproductNullCoherenceSquare_apply W n N q s t

/-- Both complete endpoint paths have a data-valued homotopy in the original cube space. -/
def original_null_coherence
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    ((coproductCubePath W n N (Path.refl q)).trans
      (coproductLeftUnitPath W n q)).Homotopy
        ((coproductSeparationPath n W c q).trans
          ((genLoopLeftConcatPath W n q N).trans (genLoopRightUnitPath n q))) :=
  coproductSeparationNullCoherence W n N q

/-- All homotopy, path and spatial coordinates retain the complete boundary. -/
theorem original_whole_boundary
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (s t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductSeparationNullCoherence W n N q (s, t) z = W.kBasepoint :=
  coproductSeparationNullCoherence_boundary W n N q s t z hz

/-- Degree zero uses the same actual null path, with no commuting of the two spatial factors. -/
def original_degree_zero
    {c : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint}
    (N : Path c GenLoop.const) (q : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint) :
    ((coproductCubePath W 0 N (Path.refl q)).trans
      (coproductLeftUnitPath W 0 q)).Homotopy
        ((coproductSeparationPath 0 W c q).trans
          ((genLoopLeftConcatPath W 0 q N).trans (genLoopRightUnitPath 0 q))) :=
  coproductSeparationNullCoherence W 0 N q

end ColibTest.CompactCoproductNullCoherence
