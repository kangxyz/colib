/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexTriangleLift

/-!
# Exact postcomposition of the native prespectrum simplex family

Postcomposition keeps every original simplex coordinate, including for the
based-loop space at level zero. Adapted from the postcomposition declarations of
`Quillen/Waldhausen/SConstruction/Iterated/SimplexWhiskering.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory Opposite Topology
open scoped Simplicial Topology unitInterval

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet

variable {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}

theorem stageTransformationSimplex_postcomp (r : ℕ) (S : ModelSimplex V W k) (J : W ⟶ T) :
    stageTransformationSimplex r (S.postcomp J) =
      stageTransformationSimplex r S ≫ (stages r).map J := by
  ext n z : 4
  exact stageSimplexFunction_postcomp r S J n z.1 z.2

theorem stageSimplexRealization_postcomp (r : ℕ) (S : ModelSimplex V W k) (J : W ⟶ T)
    (x : stageSpace r V) (z : |(Δ[k] : SSet.{u})|) :
    stageSimplexRealization r (S.postcomp J) (x, z) =
      SSet.toTop.map ((stages r).map J) (stageSimplexRealization r S (x, z)) := by
  change SSet.toTop.map (stageTransformationSimplex r (S.postcomp J))
      ((realizationProductSimplexIso ((stages r).obj V) k).inv (x, z)) = _
  rw [stageTransformationSimplex_postcomp, Functor.map_comp]
  rfl

theorem prespectrumSimplexFamily_postcomp (S : ModelSimplex V W k) (J : W ⟶ T)
    (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (S.postcomp J) n (z, x) =
      (prespectrumMap J).map n (prespectrumSimplexFamily S n (z, x)) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact stageSimplexRealization_postcomp 0 S J (x t) _
  | succ n => exact stageSimplexRealization_postcomp n S J x _

end CategoryTheory.Waldhausen.IteratedS
