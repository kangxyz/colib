/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.HomotopyFiber.LES
public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackLoopShift

/-!
# Identity self-homotopies and the original connecting map

A whole strictly commuting square of based identity self-homotopies acts on
the original path-space fiber. The source point follows its given homotopy;
the entire stored path is postcomposed with the given target homotopy.

The actual loop inclusion intertwines these whole homotopies. Combining its
operation naturality with the proved signed loop-shift formula shows that the
original connecting map from pi3 to pi2 anti-commutes with the original
self-track operation from pi2 to pi3. No action-triviality or group-level
compatibility law is assumed. Applying this to a localization still requires
comparison with its actual supported-category self-homotopy.
-/
/-! Implementation provenance: `Quillen/Topology/HomotopyFiber/SelfHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original path-space fiber,
whole self-homotopies, basepoints and negative connecting sign are retained. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
open Topology.IdentityTrack HomotopyGroup

universe u v

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Act on each original stored fiber path using a whole strict homotopy square. -/
def identityHomotopy (f : C(X, Y)) (y : Y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hY : ∀ t, HY (t, y) = y)
    (hsq : ∀ t a, HY (t, f a) = f (HX (t, a))) :
    (ContinuousMap.id (HomotopyFiber f y)).Homotopy
      (ContinuousMap.id (HomotopyFiber f y)) where
  toFun z :=
    ⟨(HX (z.1, z.2.1.1),
      ⟨fun s => HY (z.1, z.2.1.2 s), by fun_prop⟩),
      (congrArg (fun a => HY (z.1, a)) z.2.2.1).trans (hsq z.1 z.2.1.1),
      (congrArg (fun a => HY (z.1, a)) z.2.2.2).trans (hY z.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × HomotopyFiber f y) × unitInterval =>
        HY (z.1.1, z.1.2.1.2 z.2))
      fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact HX.apply_zero z.1.1
    · apply ContinuousMap.ext
      intro s
      exact HY.apply_zero (z.1.2 s)
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact HX.apply_one z.1.1
    · apply ContinuousMap.ext
      intro s
      exact HY.apply_one (z.1.2 s)

/-- The source follows the originally supplied source homotopy. -/
@[simp] theorem identityHomotopy_source (f : C(X, Y)) (y : Y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hY : ∀ t, HY (t, y) = y) (hsq : ∀ t a, HY (t, f a) = f (HX (t, a)))
    (t : unitInterval) (z : HomotopyFiber f y) :
    (identityHomotopy f y HX HY hY hsq (t, z)).1.1 = HX (t, z.1.1) := rfl

/-- Every point of the stored path follows the originally supplied target homotopy. -/
@[simp] theorem identityHomotopy_path (f : C(X, Y)) (y : Y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hY : ∀ t, HY (t, y) = y) (hsq : ∀ t a, HY (t, f a) = f (HX (t, a)))
    (t s : unitInterval) (z : HomotopyFiber f y) :
    (identityHomotopy f y HX HY hY hsq (t, z)).1.2 s = HY (t, z.1.2 s) := rfl

/-- The entire fiber homotopy fixes the original constant-path basepoint. -/
theorem identityHomotopy_based (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hX : ∀ t, HX (t, x) = x) (hY : ∀ t, HY (t, y) = y)
    (hsq : ∀ t a, HY (t, f a) = f (HX (t, a))) (t : unitInterval) :
    identityHomotopy f y HX HY hY hsq (t, basepoint f y x h) = basepoint f y x h := by
  apply Subtype.ext
  apply Prod.ext
  · exact hX t
  · apply ContinuousMap.ext
    intro s
    exact hY t

/-- Original loop inclusion intertwines the whole looped and fiber self-homotopies. -/
theorem identityHomotopy_loopInclusion (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hX : ∀ t, HX (t, x) = x) (hY : ∀ t, HY (t, y) = y)
    (hsq : ∀ t a, HY (t, f a) = f (HX (t, a)))
    (t : unitInterval) (γ : Path y y) :
    identityHomotopy f y HX HY hY hsq (t, loopInclusion f y x h γ) =
      loopInclusion f y x h (loopedHomotopy HY hY (t, γ)) := by
  apply Subtype.ext
  apply Prod.ext
  · exact hX t
  · rfl

/-- The whole strict square gives operation naturality along original loop inclusion. -/
theorem operation_loopInclusion (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hX : ∀ t, HX (t, x) = x) (hY : ∀ t, HY (t, y) = y)
    (hsq : ∀ t a, HY (t, f a) = f (HX (t, a)))
    (m : ℕ) (a : HomotopyGroup.Pi (m + 1) (Path y y) (Path.refl y)) :
    piMap (m + 1) (loopInclusion f y x h) (loopInclusion_refl f y x h)
        (IdentityTrack.operation (loopedHomotopy HY hY) (loopedHomotopy_based HY hY) m a) =
      IdentityTrack.operation (identityHomotopy f y HX HY hY hsq)
        (identityHomotopy_based f x y h HX HY hX hY hsq) m
        (piMap m (loopInclusion f y x h) (loopInclusion_refl f y x h) a) :=
  IdentityTrack.operation_natural (loopedHomotopy HY hY) (loopedHomotopy_based HY hY)
    (identityHomotopy f y HX HY hY hsq)
    (identityHomotopy_based f x y h HX HY hX hY hsq)
    (loopInclusion f y x h) (loopInclusion_refl f y x h)
    (fun t γ => (identityHomotopy_loopInclusion f x y h HX HY hX hY hsq t γ).symm) m a

/-- The original pi3-to-pi2 connecting map anti-commutes with the actual self-track operation. -/
theorem connectingHom_operation (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hX : ∀ t, HX (t, x) = x) (hY : ∀ t, HY (t, y) = y)
    (hsq : ∀ t a, HY (t, f a) = f (HX (t, a)))
    (a : HomotopyGroup.Pi 2 Y y) :
    connectingHom f y x h 1 (IdentityTrack.operation HY hY 1 a) =
      (IdentityTrack.operation (identityHomotopy f y HX HY hY hsq)
        (identityHomotopy_based f x y h HX HY hX hY hsq) 0
        (connectingHom f y x h 0 a))⁻¹ := by
  change piMap 1 (loopInclusion f y x h) (loopInclusion_refl f y x h)
    (loopShiftMulEquiv 1 (IdentityTrack.operation HY hY 1 a)) = _
  rw [IdentityTrack.operation_loopShift, map_inv]
  exact congrArg (fun b : HomotopyGroup.Pi 2 (HomotopyFiber f y) (basepoint f y x h) => b⁻¹)
    (operation_loopInclusion f x y h HX HY hX hY hsq 0 (loopShiftMulEquiv 0 a))

end Topology.HomotopyFiber

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyFiber/SelfHomotopy.lean:33-150"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  Topology.HomotopyFiber.identityHomotopy
  Topology.HomotopyFiber.identityHomotopy_source
  Topology.HomotopyFiber.identityHomotopy_path
  Topology.HomotopyFiber.identityHomotopy_based
  Topology.HomotopyFiber.identityHomotopy_loopInclusion
  Topology.HomotopyFiber.operation_loopInclusion
  Topology.HomotopyFiber.connectingHom_operation
