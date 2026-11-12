/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.UnitOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.PullbackGeneration

/-!
# Unit ratios of generating sections

Two generators on the same open determine a unit ratio. The comparison
along the entire boundary is an equality of actual restricted coefficients.

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Correction/NormalizedUnit.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

local instance {X : Scheme.{u}} (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

/-- The coefficient of the pulled section in the pulled generating frame. -/
abbrev sectionRatioCoefficientOnPullback {W X : Scheme.{u}}
    (g : W ⟶ X) (L : X.Modules) [hL : IsInvertibleModule X L] (n d : Γ(L, ⊤))
    (hn : sectionGeneratesOnPullback g L n) : Γ(W, ⊤) :=
  @sectionRatioCoefficient W ((Modules.pullback g).obj L)
    (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback W X g L hL)
    (pullbackGlobalSections g L n) (pullbackGlobalSections g L d) hn

/-- The scalar of an automorphism of the structure module is a unit. -/
theorem isUnit_structureModuleIso_coordinate {X : Scheme.{u}}
    (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsUnit (show Γ(X, ⊤) from Modules.Hom.app (X := X) e.hom ⊤ (1 : Γ(X, ⊤))) := by
  let r : Γ(X, ⊤) := Modules.Hom.app (X := X) e.hom ⊤ (1 : Γ(X, ⊤))
  have hsurj : Function.Surjective (fun s : Γ(X, ⊤) =>
      (Modules.Hom.app (X := X) e.hom ⊤ s : Γ(X, ⊤))) :=
    (ConcreteCategory.bijective_of_isIso (Modules.Hom.app (X := X) e.hom ⊤)).2
  obtain ⟨s, hs⟩ := hsurj (1 : Γ(X, ⊤))
  have he : s * r = 1 := by
    calc
      _ = (Modules.Hom.app (X := X) e.hom ⊤ (s • (1 : Γ(X, ⊤))) : Γ(X, ⊤)) := by
        rw [Modules.Hom.app_smul, smul_eq_mul]
      _ = _ := by
        rw [smul_eq_mul, mul_one]
        exact hs
  exact ⟨⟨r, s, (mul_comm r s).trans he, he⟩, rfl⟩

/-- The original norm and target coefficients give a unit on the same open.
Their actual equality along a boundary gives boundary value one. -/
theorem exists_normQuotient_unit_on_open {X Y : Scheme.{u}} (U : Y.Opens)
    (g : X ⟶ U.toScheme) [IsFiniteLocallyFree g]
    (n : Γ(X, ⊤)) (d : Γ(U.toScheme, ⊤)) (hn : IsUnit n) (hd : IsUnit d) :
    ∃ r : Γ(Y, U), IsUnit r ∧ normTop g n * U.topIso.inv r = d ∧
      ∀ {B : Scheme.{u}} (l : B ⟶ U.toScheme),
        l.appTop (normTop g n) = l.appTop d → l.appTop (U.topIso.inv r) = 1 := by
  let hn' := hn.map (normTop g)
  let u := hn'.unit
  have hu : (u : Γ(U.toScheme, ⊤)) = normTop g n := hn'.unit_spec
  let r := U.topIso.hom ((u⁻¹ : Γ(U.toScheme, ⊤)ˣ) * hd.unit)
  have hr : U.topIso.inv r = (u⁻¹ : Γ(U.toScheme, ⊤)ˣ) * hd.unit := by
    dsimp only [r]
    exact Iso.hom_inv_id_apply U.topIso _
  refine ⟨r, (u⁻¹ * hd.unit).isUnit.map U.topIso.hom.hom, ?_, ?_⟩
  · rw [hr, hd.unit_spec, ← hu, ← mul_assoc]
    simp
  · intro B l hl
    have huB : l.appTop (u : Γ(U.toScheme, ⊤)) = l.appTop d :=
      (congrArg l.appTop hu).trans hl
    rw [hr, hd.unit_spec, map_mul, ← huB, ← map_mul]
    simp

/-- The common generator open contains both prescribed boundaries on which
the four pulled sections generate. -/
theorem exists_normQuotient_generator_open {X T T₀ B₁ B₂ : Scheme.{u}}
    (F : X ⟶ T) [IsFinite F] (L : X.Modules) [IsInvertibleModule X L]
    (τ : T ⟶ T₀) (M : T₀.Modules) [IsInvertibleModule T₀ M]
    (n d : Γ(L, ⊤)) (a b : Γ(M, ⊤))
    (m₁ : B₁ ⟶ T) (m₂ : B₂ ⟶ T)
    (hm₁ : (zeroScheme T₀ M a).comap (m₁ ≫ τ) = ⊤ ∧
      (zeroScheme T₀ M b).comap (m₁ ≫ τ) = ⊤ ∧
        (zeroScheme X L n).comap (pullback.fst F m₁) = ⊤ ∧
          (zeroScheme X L d).comap (pullback.fst F m₁) = ⊤)
    (hm₂ : (zeroScheme T₀ M a).comap (m₂ ≫ τ) = ⊤ ∧
      (zeroScheme T₀ M b).comap (m₂ ≫ τ) = ⊤ ∧
        (zeroScheme X L n).comap (pullback.fst F m₂) = ⊤ ∧
          (zeroScheme X L d).comap (pullback.fst F m₂) = ⊤) :
    ∃ U : T.Opens, Set.range m₁ ⊆ (U : Set T) ∧ Set.range m₂ ⊆ (U : Set T) ∧
      let v := pullback.fst F U.ι
      zeroScheme _ ((Modules.pullback (U.ι ≫ τ)).obj M)
          (pullbackGlobalSections (U.ι ≫ τ) M a) = ⊤ ∧
        zeroScheme _ ((Modules.pullback (U.ι ≫ τ)).obj M)
          (pullbackGlobalSections (U.ι ≫ τ) M b) = ⊤ ∧
          zeroScheme _ ((Modules.pullback v).obj L) (pullbackGlobalSections v L n) = ⊤ ∧
            zeroScheme _ ((Modules.pullback v).obj L) (pullbackGlobalSections v L d) = ⊤ := by
  let I₁ := zeroScheme X L n
  let I₂ := zeroScheme X L d
  let J₁ := (zeroScheme T₀ M a).comap τ
  let J₂ := (zeroScheme T₀ M b).comap τ
  let U₁ := normUnitOpen F I₁ J₁
  let U₂ := normUnitOpen F I₂ J₂
  let U := U₁ ⊓ U₂
  have hU {B : Scheme.{u}} (m : B ⟶ T)
      (h : (zeroScheme T₀ M a).comap (m ≫ τ) = ⊤ ∧
        (zeroScheme T₀ M b).comap (m ≫ τ) = ⊤ ∧
          (zeroScheme X L n).comap (pullback.fst F m) = ⊤ ∧
            (zeroScheme X L d).comap (pullback.fst F m) = ⊤) :
      Set.range m ⊆ (U : Set T) := by
    obtain ⟨ha, hb, hn, hd⟩ := h
    exact Set.subset_inter
      ((range_subset_normUnitOpen_iff F I₁ J₁ m).2
        ⟨(IdealSheafData.comap_comp _ _ _).symm.trans ha, hn⟩)
      ((range_subset_normUnitOpen_iff F I₂ J₂ m).2
        ⟨(IdealSheafData.comap_comp _ _ _).symm.trans hb, hd⟩)
  have h₁ : Set.range U.ι ⊆ (U₁ : Set T) := by
    rw [Scheme.Opens.range_ι]
    exact inf_le_left
  have h₂ : Set.range U.ι ⊆ (U₂ : Set T) := by
    rw [Scheme.Opens.range_ι]
    exact inf_le_right
  obtain ⟨ha, hn⟩ := (range_subset_normUnitOpen_iff F I₁ J₁ U.ι).1 h₁
  obtain ⟨hb, hd⟩ := (range_subset_normUnitOpen_iff F I₂ J₂ U.ι).1 h₂
  exact ⟨U, hU m₁ hm₁, hU m₂ hm₂, (zeroScheme_pullback (U.ι ≫ τ) M a).trans
      ((IdealSheafData.comap_comp _ _ _).trans ha),
    (zeroScheme_pullback (U.ι ≫ τ) M b).trans ((IdealSheafData.comap_comp _ _ _).trans hb),
    (zeroScheme_pullback (pullback.fst F U.ι) L n).trans hn,
    (zeroScheme_pullback (pullback.fst F U.ι) L d).trans hd⟩

/-- A prescribed boundary ratio multiplies the reverse coefficient to one
in the ring of the entire original boundary. -/
theorem sectionRatioCoefficient_mul_boundary {X W Z B : Scheme.{u}}
    (w : W ⟶ X) (j : Z ⟶ X) (i : B ⟶ W) (v : B ⟶ Z) (h : i ≫ w = v ≫ j)
    (L : X.Modules) [IsInvertibleModule X L] (n d : Γ(L, ⊤)) (c : Γ(Z, ⊤))
    (hn : zeroScheme W ((Modules.pullback w).obj L) (pullbackGlobalSections w L n) = ⊤)
    (hc : pullbackGlobalSections j L n = c • pullbackGlobalSections j L d) :
    i.appTop (sectionRatioCoefficient ((Modules.pullback w).obj L)
      (pullbackGlobalSections w L n) (pullbackGlobalSections w L d) hn) * v.appTop c = 1 := by
  let M := (Modules.pullback w).obj L
  let a := pullbackGlobalSections w L n
  let b := pullbackGlobalSections w L d
  let e := frameOfZeroSchemeTop M a hn
  let e' := Modules.framePullback i e
  have hscalar : pullbackGlobalSections i M a =
      v.appTop c • pullbackGlobalSections i M b :=
    boundary_smul_identity_after_sourceChange w j i v h L n d c hc
  have ha : (e'.hom.app ⊤ (pullbackGlobalSections i M a) : Γ(B, ⊤)) = (1 : Γ(B, ⊤)) := by
    rw [show e' = Modules.framePullback i e from rfl, Modules.framePullback_coordinate,
      show e = frameOfZeroSchemeTop M a hn from rfl, frameOfZeroSchemeTop_section, map_one]
  have hb : (e'.hom.app ⊤ (pullbackGlobalSections i M b) : Γ(B, ⊤)) =
      i.appTop (sectionRatioCoefficient M a b hn) :=
    Modules.framePullback_coordinate i e b
  have he := congrArg (fun s => (e'.hom.app ⊤ s : Γ(B, ⊤))) hscalar
  rw [ha, Modules.Hom.app_smul, hb, smul_eq_mul] at he
  exact (mul_comm _ _).trans he.symm

/-- The reverse coefficients of two generators multiply to one. -/
theorem isUnit_sectionRatioCoefficient_of_generates {X : Scheme.{u}}
    (L : X.Modules) [IsInvertibleModule X L] (n d : Γ(L, ⊤))
    (hn : zeroScheme X L n = ⊤) (hd : zeroScheme X L d = ⊤) :
    IsUnit (sectionRatioCoefficient L n d hn) := by
  let r := sectionRatioCoefficient L n d hn
  let s := sectionRatioCoefficient L d n hd
  have hr : r • n = d := sectionRatioCoefficient_smul_eq L n d hn
  have hs : s • d = n := sectionRatioCoefficient_smul_eq L d n hd
  have h : (s * r) • n = n := by rw [mul_smul, hr, hs]
  let e := frameOfZeroSchemeTop L n hn
  have he := congrArg (fun t => (e.hom.app ⊤ t : Γ(X, ⊤))) h
  have hframe : (e.hom.app ⊤ n : Γ(X, ⊤)) = (1 : Γ(X, ⊤)) :=
    frameOfZeroSchemeTop_section L n hn
  rw [Modules.Hom.app_smul, hframe, smul_eq_mul, mul_one] at he
  exact ⟨⟨r, s, (mul_comm r s).trans he, he⟩, rfl⟩

/-- A unit coefficient of a generating section is again a generating section. -/
theorem zeroScheme_top_of_unit_sectionRatioCoefficient {X : Scheme.{u}}
    (L : X.Modules) [IsInvertibleModule X L] (n d : Γ(L, ⊤))
    (hn : zeroScheme X L n = ⊤) (h : IsUnit (sectionRatioCoefficient L n d hn)) :
    zeroScheme X L d = ⊤ := by
  calc
    zeroScheme X L d = zeroScheme X L (sectionRatioCoefficient L n d hn • n) :=
      congrArg (AlgebraicGeometry.zeroScheme X L) (sectionRatioCoefficient_smul_eq L n d hn).symm
    _ = zeroScheme X L n := Stacks.Divisors.zeroScheme_smul_of_isUnit L n h
    _ = ⊤ := hn

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
