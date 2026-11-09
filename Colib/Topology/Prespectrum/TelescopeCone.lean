/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeHomotopy
public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# The original cone map into the telescope of cones

For a strict tower map, the original stage cones form a strict tower. Their complete original
nullhomotopies descend through the actual telescope, keeping telescope height, cone time and
prespectrum structure time independent. This constructs an unchanged map from the cone of the
original telescope map into the telescope of the original cones, without topological hypotheses.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/TelescopeCone.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))

/-- The original strictly commuting successor square, with both unchanged transition maps. -/
def coneTransitionSquare (i : ℕ) : Arrow.mk (a i) ⟶ Arrow.mk (a (i + 1)) :=
  Arrow.homMk (f i) (g i) (ha i).symm

/-- The actual transition of the original stage cones retains their complete cylinder. -/
def coneTransition (i : ℕ) : mappingCone (a i) ⟶ mappingCone (a (i + 1)) :=
  mappingConeMap (coneTransitionSquare E f F g a ha i)

/-- The original target telescope maps into the actual telescope of stage cones. -/
def coneInclusion : prespectrum F g ⟶
    prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) :=
  map F g (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)
    (fun i ↦ mappingConeInclusion (a i)) (by
      intro i
      apply Hom.ext
      funext k
      ext y
      rfl)

/-- The whole actual stage nullhomotopies descend with independent cone and telescope parameters.
-/
def coneNullHomotopy :
    Homotopy (map E f F g a ha ≫ coneInclusion E f F g a ha)
      (zeroHom (prespectrum E f)
        (prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha))) := by
  let H := mapHomotopy E f (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)
    (fun i ↦ a i ≫ mappingConeInclusion (a i))
    (fun i ↦ zeroHom (E i) (mappingCone (a i)))
    (by
      intro i
      apply Hom.ext
      funext k
      ext x
      exact congrArg (fun y ↦ (mappingConeInclusion (a (i + 1))).map k y)
        (congrArg (fun b ↦ b.map k x) (ha i)))
    (by
      intro i
      apply Hom.ext
      funext k
      ext x
      exact (coneTransition E f F g a ha i).map_point k)
    (fun i ↦ mappingConeHomotopy (a i)) (by intros; rfl)
  exact H.cast (by apply hom_ext; intros; rfl) (by
    apply hom_ext
    intro k i s x
    exact cylinder_point (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i s)

/-- Descend the original target map and its full actual nullhomotopy into the telescope of cones.
-/
def coneToTelescope : mappingCone (map E f F g a ha) ⟶
    prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) :=
  mappingConeDesc (map E f F g a ha) (coneInclusion E f F g a ha)
    (coneNullHomotopy E f F g a ha)

/-- The original cone inclusion is sent to the unchanged target telescope map. -/
@[simp] theorem coneToTelescope_inclusion :
    mappingConeInclusion (map E f F g a ha) ≫ coneToTelescope E f F g a ha =
      coneInclusion E f F g a ha := mappingConeInclusion_desc _ _ _

/-- Every actual target cylinder keeps its original telescope height. -/
@[simp] theorem coneToTelescope_target (k i : ℕ) (t : unitInterval) (y : (F i).space k) :
    (coneToTelescope E f F g a ha).map k
      ((mappingConeInclusion (map E f F g a ha)).map k (cylinder F g k i (t, y))) =
        cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i
          (t, (mappingConeInclusion (a i)).map k y) := rfl

/-- The original source cylinder keeps cone time and telescope height separately, without
reparameterization or a chosen finite representative. -/
@[simp] theorem coneToTelescope_cylinder (k i : ℕ) (s t : unitInterval)
    (x : (E i).space k) :
    (coneToTelescope E f F g a ha).map k
      (ReducedMappingCone.cylinder ((prespectrum E f).point k) ((prespectrum F g).point k)
        ((map E f F g a ha).map k) (s, cylinder E f k i (t, x))) =
      cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i
        (t, ReducedMappingCone.cylinder ((E i).point k) ((F i).point k) ((a i).map k) (s, x)) :=
  rfl

end Topology.LoopPrespectrum.Telescope

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeCone.lean:28-105" "adaptation"
  "Actual cone descent with independent telescope height and cone time"]
  Topology.LoopPrespectrum.Telescope.coneTransitionSquare
  Topology.LoopPrespectrum.Telescope.coneTransition
  Topology.LoopPrespectrum.Telescope.coneInclusion
  Topology.LoopPrespectrum.Telescope.coneNullHomotopy
  Topology.LoopPrespectrum.Telescope.coneToTelescope
  Topology.LoopPrespectrum.Telescope.coneToTelescope_inclusion
  Topology.LoopPrespectrum.Telescope.coneToTelescope_target
  Topology.LoopPrespectrum.Telescope.coneToTelescope_cylinder

attribute [colib_tag "COL-0376"]
  Topology.LoopPrespectrum.Telescope.coneTransitionSquare
  Topology.LoopPrespectrum.Telescope.coneTransition
  Topology.LoopPrespectrum.Telescope.coneInclusion
  Topology.LoopPrespectrum.Telescope.coneNullHomotopy
  Topology.LoopPrespectrum.Telescope.coneToTelescope
  Topology.LoopPrespectrum.Telescope.coneToTelescope_inclusion
  Topology.LoopPrespectrum.Telescope.coneToTelescope_target
  Topology.LoopPrespectrum.Telescope.coneToTelescope_cylinder
