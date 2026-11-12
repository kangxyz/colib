/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.NisnevichOverlapLift
public import Colib.CategoryTheory.Sites.RelativeCohomology.BoundaryRefinement

/-! # Signed restriction differences and ordinary Nisnevich cohomology

After restriction to another distinguished square, a difference of classes
from the two legs kills the signed overlap boundary in ordinary cohomology.

This is the relative Ext form of the correction in
`Motivic/Cohomology/A1/LocalVanishing/H1/WholeCorrection.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `18e52dd49a64eac7474f8eb71986a5db71148d1c`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w t v u

namespace AlgebraicGeometry.SheafCohomology

section Relative

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
  {U X : C} (j : U ⟶ X) [Mono j]
  (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)

private theorem relativeBoundary_map_eq_zero
    (b : (cohomologyPresheaf.{w, t} F n).obj (op X)) :
    relativeBoundary J j F n ((cohomologyPresheaf.{w, t} F n).map j.op b) = 0 := by
  change Ext (relativePresentation J j).X₂ F n at b
  simp only [relativeBoundary_apply]
  change Int.negOnePow (n + 1) •
    (relativePresentation_shortExact J j).extClass.comp
      ((Ext.mk₀ (relativePresentation J j).f).comp b (zero_add n)) (Nat.add_comm 1 n) = 0
  rw [(relativePresentation_shortExact J j).extClass_comp_assoc, smul_zero]

private theorem relativeForget_boundary_eq_zero
    (a : (cohomologyPresheaf.{w, t} F n).obj (op U)) :
    relativeForget J j F (n + 1) (relativeBoundary J j F n a) = 0 := by
  change Ext (relativePresentation J j).X₁ F n at a
  simp only [relativeBoundary_apply, Units.smul_def, map_zsmul]
  change (Int.negOnePow (n + 1) : ℤ) •
    (Ext.mk₀ (relativePresentation J j).g).comp
      ((relativePresentation_shortExact J j).extClass.comp a (Nat.add_comm 1 n))
      (zero_add (n + 1)) = 0
  rw [(relativePresentation_shortExact J j).comp_extClass_assoc _ (Nat.add_comm 1 n), smul_zero]

end Relative

private theorem relativeRestriction_congr
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max v t}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
    {U X V Y : C} (j : U ⟶ X) (j' : V ⟶ Y)
    {a a' : U ⟶ V} {b b' : X ⟶ Y} (ha : a = a') (hb : b = b')
    (h : j ≫ b = a ≫ j') (h' : j ≫ b' = a' ≫ j')
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (r : relativeH J j' F n) :
    relativeRestriction J j j' a b h F n r =
      relativeRestriction J j j' a' b' h' F n r := by
  subst a' b'
  rfl

open Scheme

variable {S : Scheme.{u}}
  [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t})]

set_option maxHeartbeats 650000 in
-- Elaborating the comparison of the two relative Ext composites uses the full square.
/-- The original ordinary class restricts to zero when every restricted
overlap class is a difference of classes from the refined legs. -/
theorem ordinary_eq_zero_of_overlap_difference
    {sq sq' : Square (SmoothSite S)} (d : sq' ⟶ sq)
    (hpb : sq.IsPullback) (hpb' : sq'.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    [IsOpenImmersion sq'.f₂₄.left] [Etale sq'.f₃₄.left]
    {Z Z' : Scheme.{u}} (z : Z ⟶ sq.X₄.left) (z' : Z' ⟶ sq'.X₄.left)
    [IsClosedImmersion z] [IsClosedImmersion z']
    (hz : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    (hz' : Set.range z' = (Set.range sq'.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)] [IsIso (pullback.snd sq'.f₃₄.left z')]
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (hL : let P := cohomologyPresheaf.{w, t} F n
      ∀ f : P.obj (op sq.X₁),
        ∃ a : P.obj (op sq'.X₂), ∃ b : P.obj (op sq'.X₃),
          P.map sq'.f₁₂.op a - P.map sq'.f₁₃.op b = P.map d.τ₁.op f)
    (e : (cohomologyPresheaf.{w, t} F (n + 1)).obj (op sq.X₄))
    (hU : (cohomologyPresheaf.{w, t} F (n + 1)).map sq.f₂₄.op e = 0)
    (hV : (cohomologyPresheaf.{w, t} F (n + 1)).map sq.f₃₄.op e = 0) :
    (cohomologyPresheaf.{w, t} F (n + 1)).map d.τ₄.op e = 0 := by
  let J := SmoothSite.nisnevichTopology S
  let P := cohomologyPresheaf.{w, t} F n
  let : Mono sq.f₂₄ := (SmoothSite.forgetScheme S).mono_of_mono_map
    (inferInstanceAs (Mono sq.f₂₄.left))
  let : Mono sq'.f₂₄ := (SmoothSite.forgetScheme S).mono_of_mono_map
    (inferInstanceAs (Mono sq'.f₂₄.left))
  let : Mono sq.f₁₃ := hpb.mono_f₁₃
  let : Mono sq'.f₁₃ := hpb'.mono_f₁₃
  obtain ⟨r, f, hr, hf⟩ := exists_nisnevich_overlap_boundary_lift sq hpb z hz F n e hU hV
  let r' := relativeRestriction J sq'.f₂₄ sq.f₂₄ d.τ₂ d.τ₄ d.comm₂₄ F (n + 1) r
  let restrict' := relativeRestriction J
    sq'.f₁₃ sq'.f₂₄ sq'.f₁₂ sq'.f₃₄ sq'.fac.symm F (n + 1)
  let : IsIso restrict' := isIso_relativeRestriction_nisnevich sq' hpb' z' hz' F (n + 1)
  have hc₁ :
      sq'.f₁₃ ≫ (sq'.f₃₄ ≫ d.τ₄) = (sq'.f₁₂ ≫ d.τ₂) ≫ sq.f₂₄ := by
    rw [← Category.assoc, ← sq'.fac, Category.assoc, d.comm₂₄, ← Category.assoc]
  have hc₂ :
      sq'.f₁₃ ≫ (d.τ₃ ≫ sq.f₃₄) = (d.τ₁ ≫ sq.f₁₂) ≫ sq.f₂₄ := by
    rw [← Category.assoc, d.comm₁₃, Category.assoc, ← sq.fac, ← Category.assoc]
  have hres : restrict' r' = relativeBoundary J sq'.f₁₃ F n (P.map d.τ₁.op f) := by
    calc
      _ = relativeRestriction J sq'.f₁₃ sq.f₁₃ d.τ₁ d.τ₃ d.comm₁₃ F (n + 1)
          ((relativeNisnevichExcisionIso sq hpb z hz F (n + 1)).hom r) := by
        change relativeRestriction J sq'.f₁₃ sq'.f₂₄ sq'.f₁₂ sq'.f₃₄ sq'.fac.symm F (n + 1) r' =
          relativeRestriction J sq'.f₁₃ sq.f₁₃ d.τ₁ d.τ₃ d.comm₁₃ F (n + 1)
            (relativeRestriction J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F (n + 1) r)
        dsimp only [r']
        rw [relativeRestriction_comp J sq'.f₁₃ sq'.f₂₄ sq.f₂₄
          sq'.f₁₂ sq'.f₃₄ sq'.fac.symm d.τ₂ d.τ₄ d.comm₂₄ hc₁ F (n + 1) r,
          relativeRestriction_comp J sq'.f₁₃ sq.f₁₃ sq.f₂₄
            d.τ₁ d.τ₃ d.comm₁₃ sq.f₁₂ sq.f₃₄ sq.fac.symm hc₂ F (n + 1) r]
        exact relativeRestriction_congr J sq'.f₁₃ sq.f₂₄ d.comm₁₂ d.comm₃₄
          hc₁ hc₂ F (n + 1) r
      _ = _ := by rw [hf, relativeBoundary_restriction]
  obtain ⟨a, b, hab⟩ := hL f
  have hb := relativeBoundary_map_eq_zero J sq'.f₁₃ F n b
  have hr' : r' = relativeBoundary J sq'.f₂₄ F n a := by
    apply (ConcreteCategory.bijective_of_isIso restrict').injective
    rw [hres, ← hab, map_sub, hb, sub_zero]
    exact (relativeBoundary_restriction J sq'.f₁₃ sq'.f₂₄
      sq'.f₁₂ sq'.f₃₄ sq'.fac.symm F n a).symm
  have hforget := relativeForget_restriction J sq'.f₂₄ sq.f₂₄ d.τ₂ d.τ₄ d.comm₂₄ F (n + 1) r
  change relativeForget J sq'.f₂₄ F (n + 1) r' = _ at hforget
  rw [← hr, ← hforget, hr', relativeForget_boundary_eq_zero]

end AlgebraicGeometry.SheafCohomology
