/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Actual row interchanges under parameter looping

An original based row interchange acts pointwise on the independent old loop. Its index is
unchanged. The two-structure identity, strict map squares, and whole homotopy squares therefore
pass to parameter-correct looping without identifying either loop with a structure coordinate.
These are local closure lemmas; an application must supply its actual original interchange.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowInterchange
variable {E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))

/-- The same row interchange acts pointwise on the original independent parameter loop. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:29-33"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def parameterLoop (k : ℕ) :
    C((parameterLooping E).space (k + 3), (parameterLooping E).space (k + 3)) :=
  basedLoopMap (qE k) (hE k)

/-- The original loop coordinate is unchanged. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:34-38"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem parameterLoop_apply (k : ℕ) (γ : Path (E.point (k + 3)) (E.point (k + 3)))
    (r : unitInterval) :
    Path.toContinuousMap (parameterLoop qE hE k γ) r = qE k (γ r) := rfl

/-- The constant old loop stays constant. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:39-43"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem parameterLoop_point (k : ℕ) :
    parameterLoop qE hE k ((parameterLooping E).point (k + 3)) =
      (parameterLooping E).point (k + 3) := basedLoopMap_refl _ _

/-- An actual involution stays involutive on every old loop. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:44-52"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem parameterLoop_involutive (k : ℕ) (hq : Function.Involutive (qE k)) :
    Function.Involutive (parameterLoop qE hE k) := by
  intro γ
  change Path (E.point (k + 3)) (E.point (k + 3)) at γ
  apply Path.ext
  funext r
  exact hq (γ r)

/-- Both structure times interchange, independently of the unshifted old loop parameter. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:53-70"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem parameterLoop_structure
    (hswap : ∀ k (x : E.space (k + 1)) (s t : unitInterval),
      qE k (E.structureMap (k + 2) (E.structureMap (k + 1) x s) t) =
        E.structureMap (k + 2) (E.structureMap (k + 1) x t) s)
    (k : ℕ) (γ : (parameterLooping E).space (k + 1)) (s t : unitInterval) :
    parameterLoop qE hE k ((parameterLooping E).structureMap (k + 2)
      ((parameterLooping E).structureMap (k + 1) γ s) t) =
        (parameterLooping E).structureMap (k + 2)
          ((parameterLooping E).structureMap (k + 1) γ t) s := by
  change Path (E.point (k + 1)) (E.point (k + 1)) at γ
  apply Path.ext
  funext r
  exact hswap k (γ r) s t

variable (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))

/-- Actual strict row squares pass through the original parameter-looping map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:71-81"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem parameterLoop_map (f : E ⟶ F)
    (hf : ∀ k x, qF k (f.map (k + 3) x) = f.map (k + 3) (qE k x))
    (k : ℕ) (γ : (parameterLooping E).space (k + 3)) :
    parameterLoop qF hF k ((parameterLoopingMap f).map (k + 3) γ) =
      (parameterLoopingMap f).map (k + 3) (parameterLoop qE hE k γ) := by
  change Path (E.point (k + 3)) (E.point (k + 3)) at γ
  apply Path.ext
  funext r
  exact hf k (γ r)

/-- The whole prescribed homotopy square passes to looping with its time unchanged. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeParameterLooping.lean:82-93"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem parameterLoop_homotopy {f g : E ⟶ F} (H : Homotopy f g)
    (hH : ∀ k t x, qF k (H.level (k + 3) (t, x)) =
      H.level (k + 3) (t, qE k x))
    (k : ℕ) (t : unitInterval) (γ : (parameterLooping E).space (k + 3)) :
    parameterLoop qF hF k (H.parameterLooping.level (k + 3) (t, γ)) =
      H.parameterLooping.level (k + 3) (t, parameterLoop qE hE k γ) := by
  change Path (E.point (k + 3)) (E.point (k + 3)) at γ
  apply Path.ext
  funext r
  exact hH k t (γ r)

end Topology.LoopPrespectrum.RowInterchange
