/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.Basic
public import Colib.Topology.HomotopyFiber.BasepointTransport
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-!
# The low-degree kernel chase in the actual homotopy pullback

An original source loop killed by the original map lifts to the canonical
homotopy fiber. Concatenation with the displayed pullback path transports it
to the required parameter fiber. An actual unit-removal path corrects its
basepoint, with both projection tracks literally constant. This gives exact
source and parameter classes, without an assumed fundamental-group pushout.
-/

/-! Adapted from `Quillen/Topology/HomotopyPullback/PiOneKernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace Topology.HomotopyPullback
variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
variable (f : C(X, B)) (g : C(A, B))

/-- The original parameter fiber includes in the actual path-space pullback. -/
def fiberInclusion (a : A) : C(HomotopyFiber f (g a), HomotopyPullback f g) where
  toFun z := ⟨(a, z.val), z.property⟩
  continuous_toFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The complete stored path at an arbitrary pullback point. -/
def pointPath (z : HomotopyPullback f g) :
    Path (f (sourceProjection f g z)) (g (baseProjection f g z)) :=
  ⟨z.val.2.2, z.property.1, z.property.2⟩

/-- Transport the canonical source fiber along the actual stored path, then
include in the original pullback. -/
def transportedFiberInclusion (z : HomotopyPullback f g) :
    C(HomotopyFiber f (f (sourceProjection f g z)), HomotopyPullback f g) :=
  (fiberInclusion f g (baseProjection f g z)).comp
    (HomotopyFiber.basepointTransportEquiv f (pointPath f g z)).toFun

/-- Removing the initial constant segment gives the exact required basepoint,
while keeping both original projection coordinates fixed for the entire path. -/
def transportedFiberUnitPath (z : HomotopyPullback f g) :
    Path (transportedFiberInclusion f g z
      (HomotopyFiber.basepoint f (f (sourceProjection f g z))
        (sourceProjection f g z) rfl)) z where
  toFun t := ⟨(z.val.1, z.val.2.1,
      (Path.delayReflLeft t (pointPath f g z)).toContinuousMap),
    (Path.delayReflLeft t (pointPath f g z)).source,
    (Path.delayReflLeft t (pointPath f g z)).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    apply Continuous.prodMk continuous_const
    exact continuous_induced_dom.comp
      (Path.continuous_delayReflLeft.comp (continuous_id.prodMk continuous_const))
  source' := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    change (Path.delayReflLeft 0 (pointPath f g z)).toContinuousMap =
      (HomotopyFiber.basepointTransportEquiv f (pointPath f g z)
        (HomotopyFiber.basepoint f (f (sourceProjection f g z))
          (sourceProjection f g z) rfl)).val.2
    rw [HomotopyFiber.basepointTransportEquiv_path, Path.delayReflLeft_zero]
    rfl
  target' := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    change (Path.delayReflLeft 1 (pointPath f g z)).toContinuousMap = z.val.2.2
    rw [Path.delayReflLeft_one]
    rfl

/-- The unit correction has a literally constant original-source track. -/
@[simp] theorem transportedFiberUnitPath_source (z : HomotopyPullback f g) :
    (transportedFiberUnitPath f g z).map (sourceProjection f g).continuous =
      Path.refl (sourceProjection f g z) := by
  ext t
  rfl

/-- The unit correction has a literally constant parameter track. -/
@[simp] theorem transportedFiberUnitPath_base (z : HomotopyPullback f g) :
    (transportedFiberUnitPath f g z).map (baseProjection f g).continuous =
      Path.refl (baseProjection f g z) := by
  ext t
  rfl

/-- A killed original Pi-one class lifts at the exact displayed pullback point,
with exactly that source class and trivial parameter class. -/
theorem exists_piOne_of_map_eq_one (z : HomotopyPullback f g)
    (β : HomotopyGroup.Pi 1 X (sourceProjection f g z))
    (hβ : HomotopyGroup.piMap 0 f rfl β = 1) :
    ∃ sP : HomotopyGroup.Pi 1 (HomotopyPullback f g) z,
      HomotopyGroup.piMap 0 (sourceProjection f g) rfl sP = β ∧
      HomotopyGroup.piMap 0 (baseProjection f g) rfl sP = 1 := by
  obtain ⟨τ, hτ⟩ := (HomotopyFiber.mem_range_projection_iff f
    (f (sourceProjection f g z)) (sourceProjection f g z) rfl β).mpr hβ
  let ρ := HomotopyGroup.piMap 0 (transportedFiberInclusion f g z) rfl τ
  refine ⟨pathTransport (transportedFiberUnitPath f g z) 1 ρ, ?_, ?_⟩
  · have hn := pathTransport_naturality (sourceProjection f g)
      (transportedFiberUnitPath f g z) 1 ρ
    change pathTransport (x₀ := sourceProjection f g z) (x₁ := sourceProjection f g z)
      _ 1 _ = _ at hn
    rw [transportedFiberUnitPath_source, pathTransport_refl] at hn
    refine hn.symm.trans ?_
    change HomotopyGroup.map (N := Fin 1) (sourceProjection f g) rfl
      (HomotopyGroup.map (transportedFiberInclusion f g z) rfl τ) = β
    rw [← HomotopyGroup.map_comp]
    exact hτ
  · have hn := pathTransport_naturality (baseProjection f g)
      (transportedFiberUnitPath f g z) 1 ρ
    change pathTransport (x₀ := baseProjection f g z) (x₁ := baseProjection f g z)
      _ 1 _ = _ at hn
    rw [transportedFiberUnitPath_base, pathTransport_refl] at hn
    refine hn.symm.trans ?_
    change HomotopyGroup.map (N := Fin 1) (baseProjection f g) rfl
      (HomotopyGroup.map (transportedFiberInclusion f g z) rfl τ) = 1
    rw [← HomotopyGroup.map_comp]
    change HomotopyGroup.piMap 0 (ContinuousMap.const _ (baseProjection f g z)) rfl τ = 1
    simp only [HomotopyGroup.piMap, HomotopyGroup.mapHom_const, MonoidHom.one_apply]

/-- The actual gap surjection and the displayed kernel inclusion force the
original source leg to be injective on Pi one. No commutativity is used. -/
theorem piOne_injective_of_gap_surjective
    {W : Type u} [TopologicalSpace W] (k : C(W, HomotopyPullback f g)) (w : W)
    (hk : Function.Surjective (HomotopyGroup.piMap 0 k (x := w) rfl))
    (hker : (HomotopyGroup.piMap 0 ((baseProjection f g).comp k) (x := w) rfl).ker ≤
      (HomotopyGroup.piMap 0 ((sourceProjection f g).comp k) (x := w) rfl).ker) :
    Function.Injective (HomotopyGroup.piMap 0 f (x := sourceProjection f g (k w)) rfl) := by
  apply (injective_iff_map_eq_one _).mpr
  intro β hβ
  obtain ⟨sP, hsP, hsP₀⟩ := exists_piOne_of_map_eq_one f g (k w) β hβ
  obtain ⟨a, rfl⟩ := hk sP
  have ha : a ∈ (HomotopyGroup.piMap 0 ((baseProjection f g).comp k) (x := w) rfl).ker := by
    change HomotopyGroup.piMap 0 ((baseProjection f g).comp k) rfl a = 1
    rw [HomotopyGroup.piMap, HomotopyGroup.mapHom_comp k rfl (baseProjection f g) rfl]
    exact hsP₀
  have ha' : HomotopyGroup.piMap 0 ((sourceProjection f g).comp k) rfl a = 1 := hker ha
  rw [HomotopyGroup.piMap, HomotopyGroup.mapHom_comp k rfl (sourceProjection f g) rfl] at ha'
  exact hsP.symm.trans ha'

end Topology.HomotopyPullback
