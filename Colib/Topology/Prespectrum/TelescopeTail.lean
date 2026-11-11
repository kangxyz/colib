/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeStableMapExt

/-!
# Actual forward tail map of the original reduced telescope

The forward map uses the unchanged original transition at every cylinder. The reverse map is
the literal shifted-stage inclusion. Original stage homotopies show their stable maps are
inverse under stagewise T1, without assuming stability of any stage transition.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The actual forward tail map applies the original transition at the same cylinder height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:27"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
def toTail : prespectrum E f ⟶
    prespectrum (fun i => E (i + 1)) (fun i => f (i + 1)) :=
  map E f (fun i => E (i + 1)) (fun i => f (i + 1)) f (fun _i => rfl)

/-- The literal shifted-stage inclusion into the unchanged original telescope. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:32"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
def tailInclusion : prespectrum (fun i => E (i + 1)) (fun i => f (i + 1)) ⟶
    prespectrum E f :=
  desc (fun i => E (i + 1)) (fun i => f (i + 1))
    (fun i => inclusion E f (i + 1)) (fun i => inclusionHomotopy E f (i + 1))

/-- Forward tail passage retains the exact original cylinder height and transition. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:38"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem toTail_cylinder (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    (toTail E f).map k (cylinder E f k i (s, x)) =
      cylinder (fun i => E (i + 1)) (fun i => f (i + 1)) k i (s, (f i).map k x) := rfl

/-- Reverse tail inclusion retains the original height and shifts only the stage label. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:43"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem tailInclusion_cylinder (k i : ℕ) (s : unitInterval) (x : (E (i + 1)).space k) :
    (tailInclusion E f).map k
      (cylinder (fun i => E (i + 1)) (fun i => f (i + 1)) k i (s, x)) =
        cylinder E f k (i + 1) (s, x) := rfl

/-- The original stage face passes through its unchanged transition. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:49"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem inclusion_toTail (i : ℕ) :
    inclusion E f i ≫ toTail E f =
      f i ≫ inclusion (fun i => E (i + 1)) (fun i => f (i + 1)) i :=
  inclusion_map _ _ _ _ _ _ i

/-- The reverse stage face is exactly the original successor-stage inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:55"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem inclusion_tailInclusion (i : ℕ) :
    inclusion (fun i => E (i + 1)) (fun i => f (i + 1)) i ≫ tailInclusion E f =
      inclusion E f (i + 1) := inclusion_desc _ _ _ _ i

/-- Forward tail passage is natural for the original strict maps of towers. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:60"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem toTail_naturality (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1)) :
    map E f F g a ha ≫ toTail F g =
      toTail E f ≫ map (fun i => E (i + 1)) (fun i => f (i + 1))
        (fun i => F (i + 1)) (fun i => g (i + 1))
        (fun i => a (i + 1)) (fun i => ha (i + 1)) := by
  apply hom_ext
  intro k i s x
  exact congrArg (fun y => cylinder (fun i => F (i + 1)) (fun i => g (i + 1)) k i (s, y))
    (congrArg (fun m => m.map k x) (ha i))

/-- The literal shifted-stage inverse is natural for the same original tower maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:72"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem tailInclusion_naturality (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1)) :
    map (fun i => E (i + 1)) (fun i => f (i + 1))
        (fun i => F (i + 1)) (fun i => g (i + 1))
        (fun i => a (i + 1)) (fun i => ha (i + 1)) ≫ tailInclusion F g =
      tailInclusion E f ≫ map E f F g a ha := by
  apply hom_ext
  intros
  rfl

variable [∀ i k, T1Space ((E i).space k)]

/-- The composite on the unchanged telescope induces the actual identity signed stable map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:85"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem toTail_comp_tailInclusion_stableMap (d : ℤ) :
    (stableHomotopyFunctor d).map (toTail E f ≫ tailInclusion E f) =
      𝟙 (stableHomotopyGroup (prespectrum E f) d) := by
  refine Eq.trans ?_ ((stableHomotopyFunctor d).map_id (prespectrum E f))
  apply stableMap_ext E f
  intro i
  have h : inclusion E f i ≫ (toTail E f ≫ tailInclusion E f) =
      f i ≫ inclusion E f (i + 1) := by
    apply Hom.ext
    funext k
    ext x
    rfl
  rw [h, Category.comp_id]
  exact ((inclusionHomotopy E f i).stableHomotopyMap_eq d).symm

/-- The composite on the actual shifted telescope induces its identity signed stable map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:101"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem tailInclusion_comp_toTail_stableMap (d : ℤ) :
    (stableHomotopyFunctor d).map (tailInclusion E f ≫ toTail E f) =
      𝟙 (stableHomotopyGroup
        (prespectrum (fun i => E (i + 1)) (fun i => f (i + 1))) d) := by
  refine Eq.trans ?_ ((stableHomotopyFunctor d).map_id
    (prespectrum (fun i => E (i + 1)) (fun i => f (i + 1))))
  apply stableMap_ext (fun i => E (i + 1)) (fun i => f (i + 1))
  intro i
  have h : inclusion (fun i => E (i + 1)) (fun i => f (i + 1)) i ≫
      (tailInclusion E f ≫ toTail E f) =
        f (i + 1) ≫ inclusion (fun i => E (i + 1)) (fun i => f (i + 1)) (i + 1) := by
    apply Hom.ext
    funext k
    ext x
    rfl
  rw [h, Category.comp_id]
  exact (Homotopy.stableHomotopyMap_eq
    (inclusionHomotopy (fun i => E (i + 1)) (fun i => f (i + 1)) i) d).symm

/-- The original forward tail map is stable without any stagewise stability premise. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:121"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem toTail_isStableEquivalence : IsStableEquivalence (toTail E f) := by
  intro d
  refine ⟨⟨(stableHomotopyFunctor d).map (tailInclusion E f), ?_, ?_⟩⟩
  · rw [← Functor.map_comp]
    exact toTail_comp_tailInclusion_stableMap E f d
  · rw [← Functor.map_comp]
    exact tailInclusion_comp_toTail_stableMap E f d

/-- The unchanged shifted-stage inclusion is stable as the inverse original signed map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeTail.lean:130"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem tailInclusion_isStableEquivalence : IsStableEquivalence (tailInclusion E f) := by
  intro d
  refine ⟨⟨(stableHomotopyFunctor d).map (toTail E f), ?_, ?_⟩⟩
  · rw [← Functor.map_comp]
    exact tailInclusion_comp_toTail_stableMap E f d
  · rw [← Functor.map_comp]
    exact toTail_comp_tailInclusion_stableMap E f d

end Topology.LoopPrespectrum.Telescope
