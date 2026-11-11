/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.RowNormalization

noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u v

namespace Topology.LoopNormalizationPrism
section
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}
variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

example (x : X) :
    normalizationHomotopy γ α N (0, x) = loopNormalizedSelfTrack (γ x) (α.evalAt x) :=
  normalizationHomotopy_zero γ α N x

example (x : X) :
    normalizationHomotopy γ α N (1, x) =
      (N.evalAt x).symm.trans ((α.evalAt x).trans (N.evalAt x)) :=
  normalizationHomotopy_one γ α N x

end
end Topology.LoopNormalizationPrism

namespace Topology.LoopNormalizationPrism
section
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}
variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

example (x : X) (hγ : γ x = Path.refl y)
    (hα : ∀ t, α (t, x) = Path.refl y) (hN : ∀ t, N (t, x) = Path.refl y)
    (r : unitInterval) :
    normalizationHomotopy γ α N (r, x) = Path.refl (Path.refl y) :=
  normalizationHomotopy_fixed γ α N x hγ hα hN r

end
end Topology.LoopNormalizationPrism

namespace Topology.LoopPrespectrum.RowRefinement
section
variable {F E : LoopPrespectrum.{u}}
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
  (f : F ⟶ spectrum E q hq) (H : Homotopy f f)
  (N : Homotopy f (zeroHom F (spectrum E q hq)))

example (k : ℕ) (r : unitInterval) :
    normalizationStage q hq f H N k (r, F.point (k + 1)) =
      Path.refl (Path.refl (E.point (k + 2))) :=
  normalizationStage_point q hq f H N k r

example (k : ℕ) (x : F.space (k + 1)) :
    normalizationStage q hq f H N k (0, x) = normalizedStage q hq f H k x :=
  normalizationStage_zero q hq f H N k x

example (k : ℕ) (x : F.space (k + 1)) :
    normalizationStage q hq f H N k (1, x) = (H.nullLoopMap N).map (k + 1) x :=
  normalizationStage_one q hq f H N k x

end
end Topology.LoopPrespectrum.RowRefinement

namespace Topology.LoopPrespectrum.RowRefinement
section
variable {F E : LoopPrespectrum.{u}}
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
  (f : F ⟶ spectrum E q hq) (H : Homotopy f f)
  (N : Homotopy f (zeroHom F (spectrum E q hq)))

example (k : ℕ) (x : F.space (k + 1))
    (r t s : unitInterval) :
    Path.toContinuousMap
      (Path.toContinuousMap ((normalizationHomotopy q hq f H N).level (k + 1) (r, x)) t) s =
        normalizationStage q hq f H N k (r, x) t s :=
  normalizationHomotopy_succ q hq f H N k x r t s

example (x : F.space 0) (r t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap ((normalizationHomotopy q hq f H N).level 0 (r, x)) t) a) s =
        normalizationStage q hq f H N 0 (r, F.structureMap 0 x a) t s :=
  normalizationHomotopy_zero q hq f H N x r t a s

end
end Topology.LoopPrespectrum.RowRefinement
