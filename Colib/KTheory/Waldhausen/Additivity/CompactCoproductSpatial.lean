/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductUnits
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopUnitPaths

public import Colib.Util.References

/-! # Actual spatial separation of compact coproduct cubes

The quotient cube is delayed into the second half and the identity cube into the first.
The complete compact parameter family is lifted before either actual unit cylinder is used.
The result retains the original traversal order `q` then `c`, including one-coordinate inputs.
-/
/-! Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductSpatial.lean` at
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
variable (n : ℕ)
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

omit [HasBinaryCoproducts C] in
/-- Actual product lifts preserve simultaneous spatial concatenation, by their two projections. -/
theorem productCubeLift_transAt
    (p₀ p₁ q₀ q₁ : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    productCubeLift W n (GenLoop.transAt 0 p₀ p₁) (GenLoop.transAt 0 q₀ q₁) =
      GenLoop.transAt 0 (productCubeLift W n p₀ q₀) (productCubeLift W n p₁ q₁) := by
  symm
  apply productCubeLift_unique
  intro z
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> exact productCubeLift_projection W n _ _ _

/-- The normalized coproduct keeps the actual simultaneous-concatenation identity. -/
theorem coproductCube_transAt
    (p₀ p₁ q₀ q₁ : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    coproductCube W n (GenLoop.transAt 0 p₀ p₁) (GenLoop.transAt 0 q₀ q₁) =
      GenLoop.transAt 0 (coproductCube W n p₀ q₀) (coproductCube W n p₁ q₁) := by
  unfold coproductCube
  rw [productCubeLift_transAt, GenLoop.postcomp_transAt]

/-- All compact family parameters enter the lift together with separation time and the cube. -/
def coproductSeparationDelayFamily {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    C(unitInterval × T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :=
  coproductCubeFamily W n
    ⟨fun z ↦ genLoopDelayLeft n (σ z.1, p z.2),
      (genLoopDelayLeft n).continuous.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk
          (p.continuous.comp continuous_snd))⟩
    ⟨fun z ↦ genLoopDelayRight n (σ z.1, q z.2),
      (genLoopDelayRight n).continuous.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk
          (q.continuous.comp continuous_snd))⟩

/-- Its literal evaluation retains the original reversed separation-time delays. -/
theorem coproductSeparationDelayFamily_apply {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (t : unitInterval) (s : T) :
    coproductSeparationDelayFamily n W p q (t, s) =
      coproductCube W n (genLoopDelayLeft n (σ t, p s))
        (genLoopDelayRight n (σ t, q s)) := rfl

/-- The complete intermediate family has the zero-left factor first in spatial traversal. -/
def coproductSeparationMiddleFamily {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :=
  (genLoopTransAtContinuousMap 0).comp
    ((coproductCubeFamily W n (ContinuousMap.const T GenLoop.const) q).prodMk
      (coproductCubeFamily W n p (ContinuousMap.const T GenLoop.const)))

/-- The actual delay homotopy ends at the two original unit inputs. -/
def coproductSeparationDelayHomotopy {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    (coproductCubeFamily W n p q).Homotopy (coproductSeparationMiddleFamily n W p q) where
  toContinuousMap := coproductSeparationDelayFamily n W p q
  map_zero_left s := by
    change coproductCube W n (genLoopDelayLeft n (σ 0, p s))
      (genLoopDelayRight n (σ 0, q s)) = coproductCube W n (p s) (q s)
    rw [unitInterval.symm_zero, genLoopDelayLeft_one, genLoopDelayRight_one]
  map_one_left s := by
    change coproductCube W n (genLoopDelayLeft n (σ 1, p s))
      (genLoopDelayRight n (σ 1, q s)) =
        GenLoop.transAt 0 (coproductCube W n GenLoop.const (q s))
          (coproductCube W n (p s) GenLoop.const)
    rw [unitInterval.symm_one, genLoopDelayLeft_zero, genLoopDelayRight_zero,
      coproductCube_transAt]

/-- The full second half is the original zero-left and zero-right unit cylinders. -/
def coproductSeparationUnitHomotopy {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    (coproductSeparationMiddleFamily n W p q).Homotopy
      ((genLoopTransAtContinuousMap 0).comp (q.prodMk p)) where
  toFun z := GenLoop.transAt 0
    (coproductLeftUnitCubeMap W n (z.1, q z.2))
    (coproductRightUnitCubeMap W n (z.1, p z.2))
  continuous_toFun := (genLoopTransAtContinuousMap 0).continuous.comp
    (((coproductLeftUnitCubeMap W n).continuous.comp
      (continuous_fst.prodMk (q.continuous.comp continuous_snd))).prodMk
      ((coproductRightUnitCubeMap W n).continuous.comp
        (continuous_fst.prodMk (p.continuous.comp continuous_snd))))
  map_zero_left s := congrArg₂ (GenLoop.transAt 0)
    (coproductLeftUnitPath W n (q s)).source (coproductRightUnitPath W n (p s)).source
  map_one_left s := congrArg₂ (GenLoop.transAt 0)
    (coproductLeftUnitPath W n (q s)).target (coproductRightUnitPath W n (p s)).target

/-- The full compact separation keeps both old half-speed paths and the q-first order. -/
def coproductSeparationFamily {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    (coproductCubeFamily W n p q).Homotopy
      ((genLoopTransAtContinuousMap 0).comp (q.prodMk p)) :=
  (coproductSeparationDelayHomotopy n W p q).trans (coproductSeparationUnitHomotopy n W p q)

/-- The first original half of the displayed separation path. -/
def coproductSeparationDelayPath
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    Path (coproductCube W n p q)
      (GenLoop.transAt 0 (coproductCube W n GenLoop.const q)
        (coproductCube W n p GenLoop.const)) :=
  (coproductSeparationDelayHomotopy n W (ContinuousMap.const Unit p)
    (ContinuousMap.const Unit q)).evalAt ()

/-- The second original half consists of the two actual unit paths. -/
def coproductSeparationUnitPath
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    Path (GenLoop.transAt 0 (coproductCube W n GenLoop.const q)
      (coproductCube W n p GenLoop.const)) (GenLoop.transAt 0 q p) :=
  (coproductSeparationUnitHomotopy n W (ContinuousMap.const Unit p)
    (ContinuousMap.const Unit q)).evalAt ()

/-- The actual compact coproduct is joined to spatial traversal of q followed by p. -/
def coproductSeparationPath
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    Path (coproductCube W n p q) (GenLoop.transAt 0 q p) :=
  (coproductSeparationFamily n W (ContinuousMap.const Unit p)
    (ContinuousMap.const Unit q)).evalAt ()

/-- Both separation halves keep the original concatenation speeds. -/
theorem coproductSeparationPath_eq
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    coproductSeparationPath n W p q =
      (coproductSeparationDelayPath n W p q).trans
        (coproductSeparationUnitPath n W p q) := rfl

/-- All compact family slices agree with the same actual separation path. -/
theorem coproductSeparationFamily_apply {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (t : unitInterval) (s : T) :
    coproductSeparationFamily n W p q (t, s) = coproductSeparationPath n W (p s) (q s) t := rfl

/-- Every separation slice retains the complete original spatial boundary. -/
theorem coproductSeparationFamily_boundary {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint))
    (t : unitInterval) (s : T) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductSeparationFamily n W p q (t, s) z = W.kBasepoint :=
  (coproductSeparationFamily n W p q (t, s)).property z hz


attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductSpatial.lean:124-129" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductCube_transAt

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductSpatial.lean:196-200" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationFamily

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductSpatial.lean:234-236" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationFamily_apply

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductSpatial.lean:239-244" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationFamily_boundary

end CategoryTheory.Waldhausen.Additivity
