/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.RelativeExcision

/-! # Actual positive-degree overlap lifts on a Nisnevich square -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Sheaf/NisnevichOverlapLift.lean`, blob
`344d2dcf35897369fa670ccc0f49f7904e4f32b6`.
The actual ordinary free-Yoneda Ext groups, signed boundary and original
restriction arrows are retained. No positive-cohomology sheaf gluing or
whole-cylinder generic-base vanishing is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w t v u

namespace AlgebraicGeometry.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
open _root_.Stacks.Cohomology.FreeYonedaUnivLE

section General
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
  {U X V Y : C} (j : U ⟶ X) (j' : V ⟶ Y)
  (a : U ⟶ V) (b : X ⟶ Y) (h : j ≫ b = a ≫ j')

/-- The relative-to-ordinary map commutes with the unchanged site restrictions. -/
theorem relativeForget_restriction
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (z : relativeH J j' F n) :
    relativeForget J j F n (relativeRestriction J j j' a b h F n z) =
      (cohomologyPresheaf.{w, t} F n).map b.op (relativeForget J j' F n z) := by
  change Ext (relativeSource J j') F n at z
  change (Ext.mk₀ (relativeSourceπ J j)).comp
      ((Ext.mk₀ (relativeSourceMap J j j' a b h)).comp z (zero_add n))
        (zero_add n) =
    (Ext.mk₀ ((freeYoneda.{t} J).map b)).comp
      ((Ext.mk₀ (relativeSourceπ J j')).comp z (zero_add n)) (zero_add n)
  simp only [Ext.mk₀_comp_mk₀_assoc, relativeSourceπ_naturality]

end General

section Nisnevich
variable {S : Scheme.{u}}
  [HasSheafify (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S)
      AddCommGrpCat.{max u t}]
  [HasExt.{w} (Sheaf (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S)
      AddCommGrpCat.{max u t})]
  (sq : Square (_root_.AlgebraicGeometry.Scheme.SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

local instance : Mono sq.f₂₄ := (_root_.AlgebraicGeometry.Scheme.SmoothSite.forgetScheme
    S).mono_of_mono_map (by
  change Mono sq.f₂₄.left
  infer_instance)

/-- A class killed on both actual legs comes from an actual overlap class.
The signed boundary and original ordinary Ext groups are unchanged. -/
theorem exists_nisnevich_overlap_boundary_lift
    (F : Sheaf (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S)
        AddCommGrpCat.{max u t}) (n : ℕ)
    (e : (cohomologyPresheaf.{w, t} F (n + 1)).obj (op sq.X₄))
    (hU : (cohomologyPresheaf.{w, t} F (n + 1)).map
        sq.f₂₄.op e = 0)
    (hV : (cohomologyPresheaf.{w, t} F (n + 1)).map
        sq.f₃₄.op e = 0) :
    letI : Mono sq.f₁₃ := hpb.mono_f₁₃
    ∃ (r : relativeH
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S) sq.f₂₄ F (n + 1))
      (f : (cohomologyPresheaf.{w, t} F n).obj (op sq.X₁)),
      relativeForget
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S) sq.f₂₄ F (n + 1) r = e ∧
      (relativeNisnevichExcisionIso sq hpb z hcomp F
          (n + 1)).hom r =
        relativeBoundary
            (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S) sq.f₁₃ F n f := by
  let : Mono sq.f₁₃ := hpb.mono_f₁₃
  dsimp only
  let J := SmoothSite.nisnevichTopology S
  obtain ⟨r, hr⟩ := relative_lift_of_restriction_zero J sq.f₂₄ F (n + 1) e hU
  have hz : relativeForget J sq.f₁₃ F (n + 1)
      ((relativeNisnevichExcisionIso sq hpb z hcomp F (n + 1)).hom r) = 0 := by
    change relativeForget J sq.f₁₃ F (n + 1)
      (relativeRestriction J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F (n + 1) r) = 0
    rw [relativeForget_restriction, hr]
    exact hV
  obtain ⟨f, hf⟩ := relativeBoundary_lift_of_forget_zero J sq.f₁₃ F n _ hz
  exact ⟨r, f, hr, hf.symm⟩

end Nisnevich
end AlgebraicGeometry.SheafCohomology
