/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen

/-!
# Section-valued points of the native additive group

Use the existing representation of global sections. The affine parameter
section preserves the original source and pulls the actual coordinate back to
its specified value.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The point of the existing additive group determined by an actual section. -/
def nativeAdditivePoint {S P : Scheme.{u}} (b : P ⟶ S) (s : Γ(P, ⊤)) :
    Over.mk b ⟶ Scheme.asOver (additiveGroupBaseChange S) S :=
  ((additiveGroupBaseChangeRepresentableBy S).homEquiv (X := Over.mk b)).symm s

/-- The structural morphism of the point is the original map to the base. -/
@[reassoc] theorem nativeAdditivePoint_over {S P : Scheme.{u}} (b : P ⟶ S) (s : Γ(P, ⊤)) :
    (nativeAdditivePoint b s).left ≫ (additiveGroupBaseChange S ↘ S) = b :=
  Over.w _

/-- The actual additive coordinate pulls back to the specified section. -/
theorem nativeAdditivePoint_coordinate {S P : Scheme.{u}} (b : P ⟶ S) (s : Γ(P, ⊤)) :
    (nativeAdditivePoint b s).left.appTop (additiveGroupBaseChangeCoordinate S) = s := by
  let e := (additiveGroupBaseChangeRepresentableBy S).homEquiv (X := Over.mk b)
  have h := additiveGroupBaseChangeRepresentableBy_apply S (nativeAdditivePoint b s)
  have he : e (nativeAdditivePoint b s) = s := e.apply_symm_apply s
  change e (nativeAdditivePoint b s) = _ at h
  rw [he] at h
  change s = ((nativeAdditivePoint b s).left ≫ pullback.fst _ _).appTop additiveCoordinate at h
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact h.symm

/-- Pullback of a section-valued point follows the actual source morphism. -/
@[reassoc] theorem nativeAdditivePoint_comp_left {S P D : Scheme.{u}}
    (b : P ⟶ S) (a : D ⟶ P) (s : Γ(P, ⊤)) :
    (nativeAdditivePoint (a ≫ b) (a.appTop s)).left = a ≫ (nativeAdditivePoint b s).left := by
  have h : nativeAdditivePoint (a ≫ b) (a.appTop s) =
      Over.homMk a rfl ≫ nativeAdditivePoint b s := by
    apply (additiveGroupBaseChangeRepresentableBy S).homEquiv.injective
    simp only [nativeAdditivePoint, (additiveGroupBaseChangeRepresentableBy S).homEquiv_comp,
      Equiv.apply_symm_apply]
    rfl
  exact congrArg (fun f => f.left) h

namespace Scheme

variable {k : Type u} [Field k] {P : Scheme.{u}} (b : P ⟶ Spec (.of k))

set_option quotPrecheck false in
local notation "τ" => (additiveGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
set_option quotPrecheck false in
local notation "c" => additiveGroupBaseChangeCoordinate (Spec (.of k))

/-- The section of the actual affine parameter product at the given scalar. -/
def nativeAdditiveParameterSection (a : k) : P ⟶ pullback b τ :=
  let s := b.appTop ((ΓSpecIso (.of k)).inv a)
  pullback.lift (𝟙 P) (nativeAdditivePoint b s).left
    ((Category.id_comp b).trans (nativeAdditivePoint_over b s).symm)

@[reassoc (attr := simp)] theorem nativeAdditiveParameterSection_fst (a : k) :
    nativeAdditiveParameterSection b a ≫ pullback.fst b τ = 𝟙 P :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem nativeAdditiveParameterSection_snd (a : k) :
    nativeAdditiveParameterSection b a ≫ pullback.snd b τ =
      (nativeAdditivePoint b (b.appTop ((ΓSpecIso (.of k)).inv a))).left :=
  pullback.lift_snd _ _ _

/-- Restricting an original section to the parameter section leaves that section intact. -/
@[simp] theorem nativeAdditiveParameterSection_appTop_fst (a : k) (r : Γ(P, ⊤)) :
    (nativeAdditiveParameterSection b a).appTop ((pullback.fst b τ).appTop r) = r := by
  rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, nativeAdditiveParameterSection_fst,
    Hom.id_appTop, ConcreteCategory.id_apply]

/-- Restriction to the parameter section evaluates the native coordinate. -/
@[simp] theorem nativeAdditiveParameterSection_appTop_coordinate (a : k) :
    (nativeAdditiveParameterSection b a).appTop ((pullback.snd b τ).appTop c) =
      b.appTop ((ΓSpecIso (.of k)).inv a) := by
  rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, nativeAdditiveParameterSection_snd]
  exact nativeAdditivePoint_coordinate b _

end Scheme
end AlgebraicGeometry
