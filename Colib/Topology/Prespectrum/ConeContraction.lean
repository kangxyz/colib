/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.StableExactness

/-!
# The actual contraction of an identity cone

The original target point travels along its cone cylinder, while a cylinder point at height `s`
moves to height `s + r - s * r`. Currying into the compact-open interval mapping space makes this
a continuous contraction of the actual quotient cone. The original structure parameter is
independent of both contraction parameters, so the contraction is a whole coherent prespectrum
homotopy. No separation, point HEP, or Omega hypothesis is needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum

variable (E : LoopPrespectrum.{u})

/-- The identity-cone contraction descends continuously while retaining the entire time family. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeContraction.lean:38"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
def mappingConeIdContractionFamily (n : ℕ) :
    C((mappingCone (𝟙 E)).space n, C(unitInterval, (mappingCone (𝟙 E)).space n)) :=
  ReducedMappingCone.desc (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n)
    (ContinuousMap.curry ⟨fun z : E.space n × unitInterval ↦
      ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n) (z.2, z.1),
      by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : (unitInterval × E.space n) × unitInterval ↦
      ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n)
        (unitInterval.symm (unitInterval.symm z.2 * unitInterval.symm z.1.1), z.1.2),
      by fun_prop⟩)
    (by intro x; ext r; simp; rfl)
    (by intro x; ext r; simp)
    (by intro s; ext r; simp)

/-- The actual reduced cone on an identity contracts through strict based prespectrum maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeContraction.lean:53"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
def mappingConeIdContraction :
    Homotopy (𝟙 (mappingCone (𝟙 E)))
      (zeroHom (mappingCone (𝟙 E)) (mappingCone (𝟙 E))) where
  level n := ⟨fun z ↦ mappingConeIdContractionFamily E n z.2 z.1,
    (mappingConeIdContractionFamily E n).uncurry.continuous.comp continuous_swap⟩
  at_zero n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact ReducedMappingCone.cylinder_zero ..
      | inr z =>
        change ReducedMappingCone.cylinder _ _ _
          (unitInterval.symm (unitInterval.symm 0 * unitInterval.symm z.1), z.2) = _
        simp
        rfl
  at_one n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact ReducedMappingCone.cylinder_one ..
      | inr z =>
        change ReducedMappingCone.cylinder _ _ _
          (unitInterval.symm (unitInterval.symm 1 * unitInterval.symm z.1), z.2) = _
        simp
        rfl
  at_point n r := ReducedMappingCone.cylinder_base ..
  comm n r q t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z => rfl

/-- Original target points follow precisely the original identity-cone cylinder. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeContraction.lean:85"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision.",
  simp]
theorem mappingConeIdContraction_inclusion (n : ℕ) (r : unitInterval) (x : E.space n) :
    (mappingConeIdContraction E).level n (r, (mappingConeInclusion (𝟙 E)).map n x) =
      ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n) (r, x) := rfl

/-- The original cylinder keeps both the contraction and cone coordinates. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeContraction.lean:91"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision.",
  simp]
theorem mappingConeIdContraction_cylinder (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (mappingConeIdContraction E).level n
      (r, ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n) (s, x)) =
        ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n)
          (unitInterval.symm (unitInterval.symm r * unitInterval.symm s), x) := rfl

/-- The original identity cone has zero actual stable homotopy groups in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeContraction.lean:98"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem mappingCone_id_stableHomotopyGroup_subsingleton (d : ℤ) :
    Subsingleton (stableHomotopyGroup (mappingCone (𝟙 E)) d) := by
  have h := (mappingConeIdContraction E).stableHomotopyMap_eq d
  rw [CategoryTheory.Functor.map_id, stableHomotopyMap_zero] at h
  have hz (a : stableHomotopyGroup (mappingCone (𝟙 E)) d) : a = 0 :=
    ConcreteCategory.congr_hom h a
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end Topology.LoopPrespectrum
