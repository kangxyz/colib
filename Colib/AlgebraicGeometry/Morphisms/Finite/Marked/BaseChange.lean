/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiber

/-!
# Base change of the full marked and residual components

The marked section base changes in its original retained open. The residual
scheme maps to the original residual open through the actual pullback maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X C Y Z W : Scheme.{u}} (f : C ⟶ X) (j : Y ⟶ C) (z : Z ⟶ X)
  (s : Z ⟶ Y) (H : IsPullback s (𝟙 Z) (j ≫ f) z) (w : W ⟶ X)

local notation "f₀" => (pullback.snd f w)
local notation "w₀" => (pullback.fst f w)
local notation "j₀" => (pullback.snd j w₀)
local notation "u₀" => (pullback.fst j w₀)
local notation "z₀" => (pullback.snd z w)
local notation "a₀" => (pullback.fst z w)

/-- The pullback retained map is the actual base change of the retained map. -/
theorem retainedMap_baseChange_isPullback : IsPullback u₀ (j₀ ≫ f₀) (j ≫ f) w :=
  ((IsPullback.of_hasPullback j w₀).flip.paste_horiz
    (IsPullback.of_hasPullback f w).flip).flip

/-- The marked section into the actual pullback retained open. -/
def baseChangeMarkedSection : pullback z w ⟶ pullback j w₀ :=
  (retainedMap_baseChange_isPullback f j w).lift (a₀ ≫ s) z₀ (by
    have hs : s ≫ j ≫ f = z := by simpa only [Category.id_comp] using H.w
    rw [Category.assoc, hs, pullback.condition])

@[reassoc (attr := simp)]
theorem baseChangeMarkedSection_fst :
    baseChangeMarkedSection f j z s H w ≫ u₀ = a₀ ≫ s :=
  (retainedMap_baseChange_isPullback f j w).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMarkedSection_target :
    baseChangeMarkedSection f j z s H w ≫ j₀ ≫ f₀ = z₀ :=
  (retainedMap_baseChange_isPullback f j w).lift_snd _ _ _

/-- The actual whole marked square remains Cartesian after arbitrary base change. -/
theorem baseChangeMarkedSection_isPullback :
    IsPullback (baseChangeMarkedSection f j z s H w) (𝟙 _) (j₀ ≫ f₀) z₀ where
  w := by simp
  isLimit' := ⟨PullbackCone.isLimitAux' _ fun t ↦ by
    refine ⟨t.snd, ?_, ?_, ?_⟩
    · change t.snd ≫ baseChangeMarkedSection f j z s H w = t.fst
      apply (retainedMap_baseChange_isPullback f j w).hom_ext
      · have ht : (t.fst ≫ u₀) ≫ (j ≫ f) = (t.snd ≫ a₀) ≫ z := by
          calc
            _ = (t.fst ≫ (j₀ ≫ f₀)) ≫ w := by
              simpa only [Category.assoc] using
                congrArg (fun k ↦ t.fst ≫ k) (retainedMap_baseChange_isPullback f j w).w
            _ = _ := by
              rw [t.condition]
              simpa only [Category.assoc] using
                congrArg (fun k ↦ t.snd ≫ k) (pullback.condition (f := z) (g := w)).symm
        let e := H.lift (t.fst ≫ u₀) (t.snd ≫ a₀) ht
        have he : e = t.snd ≫ a₀ := by simpa only [Category.comp_id] using H.lift_snd _ _ ht
        rw [Category.assoc, baseChangeMarkedSection_fst, ← Category.assoc, ← he]
        exact H.lift_fst _ _ ht
      · simp only [Category.assoc, baseChangeMarkedSection_target]
        exact t.condition.symm
    · change t.snd ≫ 𝟙 _ = t.snd
      exact Category.comp_id _
    · intro a _ ha
      change a ≫ 𝟙 _ = t.snd at ha
      simpa only [Category.comp_id] using ha⟩

section Residual

local notation "s₀" => (baseChangeMarkedSection f j z s H w)

include H in
/-- The original marked square identifies the retained section over the target. -/
theorem markedSection_original_equation : (s ≫ j) ≫ f = z := by
  simpa only [Category.assoc, Category.id_comp] using H.w

/-- The base-changed section is over the actual base-changed mark. -/
theorem markedSection_baseChange_equation : (s₀ ≫ j₀) ≫ f₀ = z₀ := by
  rw [Category.assoc, baseChangeMarkedSection_target]

variable [IsFinite f]

local notation "hs" => (markedSection_original_equation f j z s H)
local notation "hs₀" => (markedSection_baseChange_equation f j z s H w)
local notation "E" => (residualMarkedFiberOpen f j z s hs)
local notation "E₀" => (residualMarkedFiberOpen f₀ j₀ z₀ s₀ hs₀)

/-- The original map from the base-changed full fiber to the original fiber. -/
def markedFiberBaseChangeMap : pullback f₀ z₀ ⟶ pullback f z :=
  pullback.lift (pullback.fst f₀ z₀ ≫ w₀) (pullback.snd f₀ z₀ ≫ a₀) (by
    simp only [Category.assoc, pullback.condition_assoc, pullback.condition])

/-- A point of the full finite fiber lies on the marked factor precisely when
its first projection lies in the original retained open. -/
theorem mem_range_markedFiberSection_iff {X' C' Y' Z' : Scheme.{u}}
    (f' : C' ⟶ X') (j' : Y' ⟶ C') (z' : Z' ⟶ X') (s' : Z' ⟶ Y')
    (h : (s' ≫ j') ≫ f' = z') (H' : IsPullback s' (𝟙 Z') (j' ≫ f') z')
    (x : (pullback f' z' : Scheme.{u})) :
    x ∈ Set.range (markedFiberSection f' j' z' s' h) ↔
      pullback.fst f' z' x ∈ Set.range j' := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨s' b, by simp only [← Hom.comp_apply, markedFiberSection_fst]⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
      (markedFiberSection_isPullback f' j' z' s' h H') b x hb
    exact ⟨a, ha⟩

private theorem residualMarkedFiberBaseChangeMap_range :
    Set.range ((E₀).ι ≫ markedFiberBaseChangeMap f z w) ⊆ Set.range (E).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Opens.range_ι]
  change markedFiberBaseChangeMap f z w x.val ∉ Set.range (markedFiberSection f j z s hs)
  intro hx
  have h := (mem_range_markedFiberSection_iff f j z s hs H _).mp hx
  change (markedFiberBaseChangeMap f z w ≫ pullback.fst f z) x.val ∈ Set.range j at h
  have h' : pullback.fst f₀ z₀ x.val ∈ Set.range j₀ := by
    rw [Scheme.Pullback.range_snd]
    simpa only [markedFiberBaseChangeMap, pullback.lift_fst, Hom.comp_apply, Set.mem_preimage]
      using h
  exact x.property ((mem_range_markedFiberSection_iff f₀ j₀ z₀ s₀ hs₀
    (baseChangeMarkedSection_isPullback f j z s H w) _).mpr h')

/-- The base-changed residual open maps into the whole original residual open. -/
@[no_expose]
def residualMarkedFiberBaseChangeMap : (E₀).toScheme ⟶ (E).toScheme :=
  IsOpenImmersion.lift (E).ι ((E₀).ι ≫ markedFiberBaseChangeMap f z w)
    (residualMarkedFiberBaseChangeMap_range f j z s H w)

/-- The residual comparison commutes with the actual maps into the finite sources. -/
@[reassoc (attr := simp)]
theorem residualMarkedFiberBaseChangeMap_map :
    residualMarkedFiberBaseChangeMap f j z s H w ≫ residualMarkedFiberMap f j z s hs =
      residualMarkedFiberMap f₀ j₀ z₀ s₀ hs₀ ≫ w₀ := by
  have h := IsOpenImmersion.lift_fac (E).ι ((E₀).ι ≫ markedFiberBaseChangeMap f z w)
    (residualMarkedFiberBaseChangeMap_range f j z s H w)
  change residualMarkedFiberBaseChangeMap f j z s H w ≫ (E).ι = _ at h
  change residualMarkedFiberBaseChangeMap f j z s H w ≫ ((E).ι ≫ pullback.fst f z) =
    ((E₀).ι ≫ pullback.fst f₀ z₀) ≫ w₀
  rw [← Category.assoc, h]
  simp only [Category.assoc, markedFiberBaseChangeMap, pullback.lift_fst]

end Residual

end AlgebraicGeometry.Scheme
