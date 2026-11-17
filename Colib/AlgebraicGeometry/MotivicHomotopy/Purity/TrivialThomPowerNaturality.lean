/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.TrivialThomPowerBasic

/-! # Naturality along the original tower of marked affine lines -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

private theorem inverse_naturality {C : Type*} [Category* C] {A A' B B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : e.inv ≫ f = g ≫ e'.inv) : f ≫ e'.hom = e.hom ≫ g := by
  apply (cancel_epi e.inv).mp
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem comp_map_naturality {C : Type*} [Category* C] (F : C ⥤ C)
    {A A' B B' D D' : C} (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D')
    (u : A ⟶ F.obj B) (u' : A' ⟶ F.obj B') (v : B ⟶ D) (v' : B' ⟶ D')
    (ha : a ≫ u' = u ≫ F.map b) (hb : b ≫ v' = v ≫ d) :
    a ≫ (u' ≫ F.map v') = (u ≫ F.map v) ≫ F.map d := by
  rw [← Category.assoc, ha, Category.assoc, ← F.map_comp, hb, F.map_comp, Category.assoc]

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]

/-- The native abelian structure on transfer sheaves in the naturality comparison. -/
local instance instAbelianTrivialThomPowerNaturality : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

local instance instNoetherianTrivialThomPowerNaturality :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))

attribute [local irreducible] Cor.graphFunctor transferRepresentable

local notation "L" => effectiveLefschetzTwistFunctor k
local notation "M" => effectiveSmoothMotive k
local notation "P" => effectivePairMotiveFunctor k

set_option maxHeartbeats 900000 in
-- Compare the specified inverse isomorphisms through the native pair quotient.
private theorem pairMotiveIso_inv_naturality {U X V Y : Sm}
    {j : U ⟶ X} {j' : V ⟶ Y} (a : Arrow.mk j ⟶ Arrow.mk j')
    (e : (P).obj (Arrow.mk j) ≅ (M).obj X) (e' : (P).obj (Arrow.mk j') ≅ (M).obj Y)
    (he : e.inv = effectivePairMotiveQuotient k j)
    (he' : e'.inv = effectivePairMotiveQuotient k j') :
    let f := (P).map a
    let g := (M).map a.right
    e.inv ≫ f = g ≫ e'.inv := by
  intro f g
  have h : effectivePairMotiveQuotient k j ≫ f = g ≫ effectivePairMotiveQuotient k j' :=
    effectivePairMotiveQuotient_naturality_arrow k (j := j) (j' := j') a
  exact (congrArg (· ≫ f) he).trans (h.trans (congrArg (g ≫ ·) he'.symm))

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

set_option maxHeartbeats 950000 in
-- Identify the inverse comparison by its original ambient quotient.
private theorem effectiveTrivialPowerThomIso_zero_inv (X : Sm) :
    (effectiveTrivialPowerThomIso k X 0).inv =
      effectivePairMotiveQuotient k
        (closedPairOpenInclusion (affineCylinderPowerZero k X 0).left) :=
  (rfl)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1500000 in
-- Use the original support maps at the two successive stages of the tower.
/-- Naturality for every original one-line comparison gives naturality of the finite tower. -/
theorem effectiveTrivialPowerThomIso_naturality_of_append {X Y : Sm} (f : X ⟶ Y) (n : ℕ) :
    let q := fun d => closedSupportArrowMap
      (i := affineCylinderPowerZero k X d) (j := affineCylinderPowerZero k Y d)
      (f := affineCylinderPowerMap k f d) (g := f) (affineCylinderPowerZero_isPullback k f d)
    let a := fun d => (P).map (q d)
    let u := fun (W : Sm) d =>
      (effectiveAppendZeroSectionThomIso k (affineCylinderPowerZero k W d)).hom
    let e := fun (W : Sm) d => (effectiveTrivialPowerThomIso k W d).hom
    let b := fun d => (Stabilization.iterate (L) d).map ((M).map f)
    (∀ d : ℕ, a (d + 1) ≫ u Y d = u X d ≫ (L).map (a d)) →
      a n ≫ e Y n = e X n ≫ b n := by
  intro q a u e b happend
  induction n with
  | zero =>
    let j := closedPairOpenInclusion (affineCylinderPowerZero k X 0).left
    let j' := closedPairOpenInclusion (affineCylinderPowerZero k Y 0).left
    let e₀ := effectiveTrivialPowerThomIso k X 0
    let e'₀ := effectiveTrivialPowerThomIso k Y 0
    let g₀ := (M).map (q 0).right
    have hb : g₀ = b 0 := rfl
    have he : e₀.inv = effectivePairMotiveQuotient k j :=
      effectiveTrivialPowerThomIso_zero_inv k X
    have he' : e'₀.inv = effectivePairMotiveQuotient k j' :=
      effectiveTrivialPowerThomIso_zero_inv k Y
    have h : e₀.inv ≫ a 0 = g₀ ≫ e'₀.inv :=
      pairMotiveIso_inv_naturality k (j := j) (j' := j') (q 0) e₀ e'₀ he he'
    have hn : a 0 ≫ e'₀.hom = e₀.hom ≫ g₀ := inverse_naturality e₀ e'₀ (a 0) g₀ h
    exact hn.trans (congrArg (e₀.hom ≫ ·) hb)
  | succ n ih =>
    change a (n + 1) ≫ (u Y n ≫ (L).map (e Y n)) =
      (u X n ≫ (L).map (e X n)) ≫ (L).map (b n)
    exact comp_map_naturality (L) (a (n + 1)) (a n) (b n)
      (u X n) (u Y n) (e X n) (e Y n) (happend n) ih

end AlgebraicGeometry.MotivicHomotopy
