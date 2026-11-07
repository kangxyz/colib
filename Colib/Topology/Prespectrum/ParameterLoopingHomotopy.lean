/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ParameterLooping
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Parameter looping of whole prespectrum homotopies

The original homotopy acts pointwise on each actual based loop. Homotopy time, loop time,
and structure time remain independent. The time slices are the original looped maps.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ParameterLoopingHomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original whole based homotopies, independent homotopy/loop/structure times
and endpoint-arrow casts are retained in the native prespectrum owner. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}

/-- Apply the entire original homotopy to each point of an actual based loop. -/
def Homotopy.parameterLooping (H : Homotopy f g) :
    Homotopy (parameterLoopingMap f) (parameterLoopingMap g) where
  level n :=
    { toFun := fun z : unitInterval × Path (E.point n) (E.point n) ↦
        { toFun t := H.level n (z.1, z.2 t)
          continuous_toFun := by fun_prop
          source' := by rw [z.2.source]; exact H.at_point n z.1
          target' := by rw [z.2.target]; exact H.at_point n z.1 }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        change Continuous (fun z : (unitInterval × Path (E.point n) (E.point n)) × unitInterval ↦
          H.level n (z.1.1, z.1.2 z.2))
        fun_prop }
  at_zero n γ := by
    change Path (E.point n) (E.point n) at γ
    apply Path.ext
    funext t
    exact H.at_zero n (γ t)
  at_one n γ := by
    change Path (E.point n) (E.point n) at γ
    apply Path.ext
    funext t
    exact H.at_one n (γ t)
  at_point n s := by apply Path.ext; funext t; exact H.at_point n s
  comm n s γ t := by
    change Path (E.point n) (E.point n) at γ
    apply Path.ext
    funext r
    exact H.comm n s (γ r) t

/-- Homotopy and loop times retain their original independent values. -/
theorem Homotopy.parameterLooping_apply (H : Homotopy f g) (n : ℕ)
    (s t : unitInterval) (γ : Path (E.point n) (E.point n)) :
    Path.toContinuousMap (H.parameterLooping.level n (s, γ)) t =
      H.level n (s, γ t) := rfl

/-- Each whole-homotopy time slice is the unchanged parameter-looped original map. -/
theorem Homotopy.parameterLooping_at (H : Homotopy f g) (s : unitInterval) :
    H.parameterLooping.at s = parameterLoopingMap (H.at s) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

/-- The literal zero morphism remains the literal zero morphism under parameter looping. -/
theorem parameterLoopingMap_zeroHom (E F : LoopPrespectrum.{u}) :
    parameterLoopingMap (zeroHom E F) = zeroHom (parameterLooping E) (parameterLooping F) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

/-- Loop the specified whole nullhomotopy, changing only the endpoint-arrow witnesses. -/
def Homotopy.parameterLoopingNull {G : LoopPrespectrum.{u}} {a : E ⟶ F} {b : F ⟶ G}
    (H : Homotopy (a ≫ b) (zeroHom E G)) :
    Homotopy (parameterLoopingMap a ≫ parameterLoopingMap b)
      (zeroHom (LoopPrespectrum.parameterLooping E) (LoopPrespectrum.parameterLooping G)) :=
  H.parameterLooping.cast (parameterLoopingFunctor.map_comp a b)
    (parameterLoopingMap_zeroHom E G)

end Topology.LoopPrespectrum
