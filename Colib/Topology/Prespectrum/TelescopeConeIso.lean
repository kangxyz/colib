/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeCone

/-!
# Strict interchange of the original telescope and mapping cone

The reverse map descends complete interval-valued maps from each original cone before evaluating
telescope height. Compact-open currying establishes continuity without assuming that products
preserve arbitrary quotient maps. Both inverses hold on the original target and double-cylinder
generators with cone time, telescope height and structure time kept independent.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/TelescopeConeIso.lean` at
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

/-- Original stage inclusions give the strict square into the unchanged telescope arrow. -/
def coneStageSquare (i : ℕ) : Arrow.mk (a i) ⟶ Arrow.mk (map E f F g a ha) :=
  Arrow.homMk (inclusion E f i) (inclusion F g i) (inclusion_map E f F g a ha i)

/-- The original stage cone maps into the cone of the unchanged telescope map. -/
def coneStageMap (i : ℕ) : mappingCone (a i) ⟶ mappingCone (map E f F g a ha) :=
  mappingConeMap (coneStageSquare E f F g a ha i)

/-- Descend the entire telescope-height path on a cone before evaluating its height parameter.
-/
def coneStageTrackFamily (k i : ℕ) :
    C((mappingCone (a i)).space k, C(unitInterval, (mappingCone (map E f F g a ha)).space k)) :=
  ReducedMappingCone.desc ((E i).point k) ((F i).point k) ((a i).map k)
    (ContinuousMap.curry ⟨fun z : (F i).space k × unitInterval ↦
      (mappingConeInclusion (map E f F g a ha)).map k (cylinder F g k i (z.2, z.1)),
      ((mappingConeInclusion (map E f F g a ha)).map k).continuous.comp
        ((cylinder F g k i).continuous.comp continuous_swap)⟩)
    (ContinuousMap.curry ⟨fun z : (unitInterval × (E i).space k) × unitInterval ↦
      ReducedMappingCone.cylinder ((prespectrum E f).point k) ((prespectrum F g).point k)
        ((map E f F g a ha).map k) (z.1.1, cylinder E f k i (z.2, z.1.2)),
      (ReducedMappingCone.cylinder ((prespectrum E f).point k) ((prespectrum F g).point k)
        ((map E f F g a ha).map k)).continuous.comp
          (continuous_fst.fst.prodMk ((cylinder E f k i).continuous.comp
            (continuous_snd.prodMk continuous_fst.snd)))⟩)
    (by
      intro x
      ext t
      exact ReducedMappingCone.cylinder_zero _ _ _ (cylinder E f k i (t, x)))
    (by
      intro x
      ext t
      change ReducedMappingCone.cylinder _ _ _ (1, cylinder E f k i (t, x)) =
        ReducedMappingCone.inr _ _ _ (cylinder F g k i (t, (F i).point k))
      exact (ReducedMappingCone.cylinder_one ((prespectrum E f).point k)
        ((prespectrum F g).point k) ((map E f F g a ha).map k)
        (cylinder E f k i (t, x))).trans
          (congrArg (ReducedMappingCone.inr ((prespectrum E f).point k)
            ((prespectrum F g).point k) ((map E f F g a ha).map k))
            (cylinder_point F g k i t).symm))
    (by
      intro s
      ext t
      change ReducedMappingCone.cylinder _ _ _ (s, cylinder E f k i (t, (E i).point k)) =
        ReducedMappingCone.inr _ _ _ (cylinder F g k i (t, (F i).point k))
      exact (congrArg (fun x ↦ ReducedMappingCone.cylinder ((prespectrum E f).point k)
        ((prespectrum F g).point k) ((map E f F g a ha).map k) (s, x))
        (cylinder_point E f k i t)).trans
          ((ReducedMappingCone.cylinder_base ((prespectrum E f).point k)
            ((prespectrum F g).point k) ((map E f F g a ha).map k) s).trans
              (congrArg (ReducedMappingCone.inr ((prespectrum E f).point k)
                ((prespectrum F g).point k) ((map E f F g a ha).map k))
                (cylinder_point F g k i t).symm)))

/-- The exact original telescope cylinder continuously moves each whole original cone. -/
def coneStageTrack (i : ℕ) :
    Homotopy (coneStageMap E f F g a ha i)
      (coneTransition E f F g a ha i ≫ coneStageMap E f F g a ha (i + 1)) where
  level k := ⟨fun z ↦ coneStageTrackFamily E f F g a ha k i z.2 z.1,
    (coneStageTrackFamily E f F g a ha k i).uncurry.continuous.comp continuous_swap⟩
  at_zero k q := by
    induction q using Quot.inductionOn with
    | h z => cases z <;> rfl
  at_one k q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y =>
        change (mappingConeInclusion (map E f F g a ha)).map k (cylinder F g k i (1, y)) = _
        rw [cylinder_one]
        rfl
      | inr z =>
        change ReducedMappingCone.cylinder _ _ _ (z.1, cylinder E f k i (1, z.2)) = _
        rw [cylinder_one]
        rfl
  at_point k t := by
    change (mappingConeInclusion (map E f F g a ha)).map k
      (cylinder F g k i (t, (F i).point k)) = _
    rw [cylinder_point]
    rfl
  comm k s q t := by
    induction q using Quot.inductionOn with
    | h z => cases z <;> rfl

/-- Descending original cone-stage maps and their full tracks gives the reverse interchange map.
-/
def coneFromTelescope :
    prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) ⟶
      mappingCone (map E f F g a ha) :=
  desc (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)
    (coneStageMap E f F g a ha) (coneStageTrack E f F g a ha)

/-- The reverse map keeps every target telescope height literally. -/
@[simp] theorem coneFromTelescope_target (k i : ℕ) (t : unitInterval) (y : (F i).space k) :
    (coneFromTelescope E f F g a ha).map k
      (cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i
        (t, (mappingConeInclusion (a i)).map k y)) =
      (mappingConeInclusion (map E f F g a ha)).map k (cylinder F g k i (t, y)) := rfl

/-- The reverse map preserves the same two independent original cylinder coordinates. -/
@[simp] theorem coneFromTelescope_cylinder (k i : ℕ) (s t : unitInterval)
    (x : (E i).space k) :
    (coneFromTelescope E f F g a ha).map k
      (cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i
        (t, ReducedMappingCone.cylinder ((E i).point k) ((F i).point k) ((a i).map k) (s, x))) =
      ReducedMappingCone.cylinder ((prespectrum E f).point k) ((prespectrum F g).point k)
        ((map E f F g a ha).map k) (s, cylinder E f k i (t, x)) := rfl

/-- The two actual descents are inverse on the original cone, as strict prespectrum maps. -/
@[simp] theorem coneToTelescope_comp_coneFromTelescope :
    coneToTelescope E f F g a ha ≫ coneFromTelescope E f F g a ha =
      𝟙 (mappingCone (map E f F g a ha)) := by
  apply mappingCone_hom_ext
  · apply hom_ext
    intros
    rfl
  · intro k s q
    induction q using Quot.inductionOn with
    | h z => rfl

/-- The two original descents are inverse on the actual telescope of cones as well. -/
@[simp] theorem coneFromTelescope_comp_coneToTelescope :
    coneFromTelescope E f F g a ha ≫ coneToTelescope E f F g a ha =
      𝟙 (prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)) := by
  apply hom_ext
  intro k i t q
  induction q using Quot.inductionOn with
  | h z => cases z <;> rfl

/-- The actual cone of a strict telescope map is strictly isomorphic to its telescope of cones.
-/
def coneIso : mappingCone (map E f F g a ha) ≅
    prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) where
  hom := coneToTelescope E f F g a ha
  inv := coneFromTelescope E f F g a ha
  hom_inv_id := coneToTelescope_comp_coneFromTelescope E f F g a ha
  inv_hom_id := coneFromTelescope_comp_coneToTelescope E f F g a ha

end Topology.LoopPrespectrum.Telescope

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeConeIso.lean:31-155" "adaptation"
  "Actual telescope cone interchange, signed boundary and exactness with unchanged maps"]
  Topology.LoopPrespectrum.Telescope.coneStageSquare
  Topology.LoopPrespectrum.Telescope.coneStageMap
  Topology.LoopPrespectrum.Telescope.coneStageTrackFamily
  Topology.LoopPrespectrum.Telescope.coneStageTrack
  Topology.LoopPrespectrum.Telescope.coneFromTelescope
  Topology.LoopPrespectrum.Telescope.coneFromTelescope_target
  Topology.LoopPrespectrum.Telescope.coneFromTelescope_cylinder
  Topology.LoopPrespectrum.Telescope.coneToTelescope_comp_coneFromTelescope
  Topology.LoopPrespectrum.Telescope.coneFromTelescope_comp_coneToTelescope
  Topology.LoopPrespectrum.Telescope.coneIso

attribute [colib_tag "COL-0376"]
  Topology.LoopPrespectrum.Telescope.coneStageSquare
  Topology.LoopPrespectrum.Telescope.coneStageMap
  Topology.LoopPrespectrum.Telescope.coneStageTrackFamily
  Topology.LoopPrespectrum.Telescope.coneStageTrack
  Topology.LoopPrespectrum.Telescope.coneFromTelescope
  Topology.LoopPrespectrum.Telescope.coneFromTelescope_target
  Topology.LoopPrespectrum.Telescope.coneFromTelescope_cylinder
  Topology.LoopPrespectrum.Telescope.coneToTelescope_comp_coneFromTelescope
  Topology.LoopPrespectrum.Telescope.coneFromTelescope_comp_coneToTelescope
  Topology.LoopPrespectrum.Telescope.coneIso
