/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopUnit
public import Colib.Topology.Prespectrum.ConeMapHomotopy
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Original whole homotopies under suspension and parameter looping

The original moving cone-map construction acts on the given whole homotopy and the
constant identity of the literal point spectrum. Every family time is the actual
suspension-cone map of that input time slice. Looping retains the family time separately
from the original cone, loop and structure coordinates. The actual unit commutes at every
time, including for the specified whole input nullhomotopies.
-/
/-!
Implementation provenance: adapted from Quillen at
`SuspensionLoopHomotopy.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- The actual suspension-cone map retains the identity strictly. -/
@[simp] theorem suspensionConeMap_id (E : LoopPrespectrum.{u}) :
    suspensionConeMap (𝟙 E) = 𝟙 (suspensionCone E) := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

/-- The actual suspension-cone map retains the original composite strictly. -/
@[simp] theorem suspensionConeMap_comp {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G) :
    suspensionConeMap (f ≫ g) = suspensionConeMap f ≫ suspensionConeMap g := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

/-- The actual suspension-cone map of zero is the literal zero map. -/
@[simp] theorem suspensionConeMap_zeroHom (E F : LoopPrespectrum.{u}) :
    suspensionConeMap (zeroHom E F) = zeroHom (suspensionCone E) (suspensionCone F) := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro y
    change ReducedMappingCone.inr _ _ _ y = ReducedMappingCone.point _ _ _
    cases y
    rfl
  · intro z
    exact ReducedMappingCone.cylinder_base _ _ _ z.1

variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}

/-- Suspend the original whole input family through the original moving mapping-cone maps. -/
def Homotopy.suspensionCone (H : Homotopy f g) :
    Homotopy (suspensionConeMap f) (suspensionConeMap g) :=
  mappingConeMapHomotopy (A := Arrow.mk (zeroHom E pointPrespectrum))
    (B := Arrow.mk (zeroHom F pointPrespectrum))
    (s := Arrow.homMk f (𝟙 pointPrespectrum) (by
      apply Hom.ext; funext n; ext _x; rfl))
    (t := Arrow.homMk g (𝟙 pointPrespectrum) (by
      apply Hom.ext; funext n; ext _x; rfl))
    H (Homotopy.refl (𝟙 pointPrespectrum)) (fun _ _ _ ↦ rfl)

/-- The original cone coordinate and input-family clock keep their independent values. -/
theorem Homotopy.suspensionCone_cylinder (H : Homotopy f g) (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    H.suspensionCone.level n (r, ReducedMappingCone.cylinder
      (E.point n) (pointPrespectrum.point n) ((zeroHom E pointPrespectrum).map n) (s, x)) =
        ReducedMappingCone.cylinder (F.point n) (pointPrespectrum.point n)
          ((zeroHom F pointPrespectrum).map n) (s, H.level n (r, x)) := rfl

/-- Every suspension-family slice is the actual suspension map of the original input slice. -/
theorem Homotopy.suspensionCone_at (H : Homotopy f g) (r : unitInterval) :
    H.suspensionCone.at r = suspensionConeMap (H.at r) := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

/-- Parameter-loop the unchanged suspended whole family. -/
def Homotopy.suspensionLoop (H : Homotopy f g) :
    Homotopy (parameterLoopingMap (suspensionConeMap f))
      (parameterLoopingMap (suspensionConeMap g)) :=
  H.suspensionCone.parameterLooping

/-- Every looped-suspension slice is the actual map of the original input slice. -/
theorem Homotopy.suspensionLoop_at (H : Homotopy f g) (r : unitInterval) :
    H.suspensionLoop.at r = parameterLoopingMap (suspensionConeMap (H.at r)) := by
  rw [Homotopy.suspensionLoop, Homotopy.parameterLooping_at, Homotopy.suspensionCone_at]

/-- The literal unit square commutes at every original whole-family time. -/
theorem Homotopy.suspensionLoop_unit (H : Homotopy f g) (n : ℕ)
    (r : unitInterval) (x : E.space n) :
    H.suspensionLoop.level n (r, (suspensionLoopUnit E).map n x) =
      (suspensionLoopUnit F).map n (H.level n (r, x)) := by
  apply Path.ext
  funext s
  rfl

/-- Looping and suspending zero retains the literal zero endpoint. -/
theorem suspensionLoopMap_zeroHom (E F : LoopPrespectrum.{u}) :
    parameterLoopingMap (suspensionConeMap (zeroHom E F)) =
      zeroHom (parameterLooping (suspensionCone E)) (parameterLooping (suspensionCone F)) := by
  rw [suspensionConeMap_zeroHom, parameterLoopingMap_zeroHom]

end Topology.LoopPrespectrum
