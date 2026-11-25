/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrum

/-!
# Precomposition of the original prespectrum simplex family

The original simplex parameter and the independent level-zero loop time are unchanged.
Adapted from `Quillen/Waldhausen/SConstruction/Iterated/SimplexWhiskering.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory Topology Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet

variable {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}

theorem stageTransformationSimplex_precomp (r : ℕ) (S : ModelSimplex V W k) (J : T ⟶ V) :
    stageTransformationSimplex r (S.precomp J) =
      (stages r).map J ▷ Δ[k] ≫ stageTransformationSimplex r S := by
  ext n z : 4
  exact stageSimplexFunction_precomp r S J n z.1 z.2

theorem stageSimplexRealization_precomp (r : ℕ) (S : ModelSimplex V W k) (J : T ⟶ V)
    (x : stageSpace r T) (z : |(Δ[k] : SSet.{u})|) :
    stageSimplexRealization r (S.precomp J) (x, z) =
      stageSimplexRealization r S (SSet.toTop.map ((stages r).map J) x, z) := by
  let p := (realizationProductSimplexIso ((stages r).obj T) k).inv (x, z)
  have hn := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker ((stages r).map J) k) (x, z)
  change SSet.toTop.map ((stages r).map J ▷ Δ[k]) p =
    (realizationProductSimplexIso ((stages r).obj V) k).inv
      (SSet.toTop.map ((stages r).map J) x, z) at hn
  change SSet.toTop.map (stageTransformationSimplex r (S.precomp J)) p =
    SSet.toTop.map (stageTransformationSimplex r S)
      ((realizationProductSimplexIso ((stages r).obj V) k).inv
        (SSet.toTop.map ((stages r).map J) x, z))
  rw [stageTransformationSimplex_precomp, Functor.map_comp]
  exact congrArg (SSet.toTop.map (stageTransformationSimplex r S)) hn

/-- No simplex parameter changes when the original family is precomposed. -/
theorem prespectrumSimplexFamily_precomp (S : ModelSimplex V W k) (J : T ⟶ V)
    (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum T).space n) :
    prespectrumSimplexFamily (S.precomp J) n (z, x) =
      prespectrumSimplexFamily S n (z, (prespectrumMap J).map n x) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 T) (stagePoint 0 T) at x
    apply Path.ext
    funext t
    exact stageSimplexRealization_precomp 0 S J (x t) _
  | succ n => exact stageSimplexRealization_precomp n S J x _

end CategoryTheory.Waldhausen.IteratedS
