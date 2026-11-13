/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.NisnevichOverlapShrink

/-! # Original ordinary vanishing after an actual morphism of Nisnevich squares -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Sheaf/NisnevichSquareRefinement.lean`, blob
`a477de5f65ac16b3d7c3f774b3a55a0928c9dff2`.
The actual ordinary free-Yoneda Ext groups, signed boundary and original
restriction arrows are retained. No positive-cohomology sheaf gluing or
whole-cylinder generic-base vanishing is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w t u
namespace AlgebraicGeometry.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.Stacks.Cohomology.FreeYonedaUnivLE
variable {S : Scheme.{u}}
  [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t})]
  {sq sq' : Square (SmoothSite S)} (d : sq' ⟶ sq)

/-- Relative restriction commutes with the complete original square, including
an actual change of its base object. -/
theorem relativeRestriction_square_naturality
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (q : relativeH (SmoothSite.nisnevichTopology S) sq.f₂₄ F n) :
    relativeRestriction (SmoothSite.nisnevichTopology S) sq'.f₁₃ sq'.f₂₄
        sq'.f₁₂ sq'.f₃₄ sq'.fac.symm F n
        (relativeRestriction (SmoothSite.nisnevichTopology S) sq'.f₂₄ sq.f₂₄
          d.τ₂ d.τ₄ d.comm₂₄ F n q) =
      relativeRestriction (SmoothSite.nisnevichTopology S) sq'.f₁₃ sq.f₁₃
        d.τ₁ d.τ₃ d.comm₁₃ F n
        (relativeRestriction (SmoothSite.nisnevichTopology S) sq.f₁₃ sq.f₂₄
          sq.f₁₂ sq.f₃₄ sq.fac.symm F n q) := by
  let J := SmoothSite.nisnevichTopology S
  have h₁ : sq'.f₁₃ ≫ (sq'.f₃₄ ≫ d.τ₄) = (sq'.f₁₂ ≫ d.τ₂) ≫ sq.f₂₄ := by
    rw [← Category.assoc, ← sq'.fac, Category.assoc, d.comm₂₄, ← Category.assoc]
  have h₂ : sq'.f₁₃ ≫ (d.τ₃ ≫ sq.f₃₄) = (d.τ₁ ≫ sq.f₁₂) ≫ sq.f₂₄ := by
    rw [← Category.assoc, d.comm₁₃, Category.assoc, ← sq.fac, ← Category.assoc]
  rw [relativeRestriction_comp J sq'.f₁₃ sq'.f₂₄ sq.f₂₄
    sq'.f₁₂ sq'.f₃₄ sq'.fac.symm d.τ₂ d.τ₄ d.comm₂₄ h₁,
    relativeRestriction_comp J sq'.f₁₃ sq.f₁₃ sq.f₂₄
    d.τ₁ d.τ₃ d.comm₁₃ sq.f₁₂ sq.f₃₄ sq.fac.symm h₂]
  simp only [d.comm₁₂, d.comm₃₄]

/-- A genuine square refinement that kills the original overlap representative
kills the original class restricted along the actual bottom-right map. -/
theorem ordinary_restriction_eq_zero_of_square_refinement
    (hpb' : sq'.IsPullback) [Mono sq.f₁₃] [IsOpenImmersion sq'.f₂₄.left]
    [Etale sq'.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq'.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq'.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq'.f₃₄.left z)]
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (e : (cohomologyPresheaf.{w, t} F (n + 1)).obj (op sq.X₄))
    (q : relativeH (SmoothSite.nisnevichTopology S) sq.f₂₄ F (n + 1))
    (f : (cohomologyPresheaf.{w, t} F n).obj (op sq.X₁))
    (hq : relativeForget (SmoothSite.nisnevichTopology S) sq.f₂₄ F (n + 1) q = e)
    (hf : relativeRestriction (SmoothSite.nisnevichTopology S) sq.f₁₃ sq.f₂₄
      sq.f₁₂ sq.f₃₄ sq.fac.symm F (n + 1) q =
        relativeBoundary (SmoothSite.nisnevichTopology S) sq.f₁₃ F n f)
    (hz : (cohomologyPresheaf.{w, t} F n).map d.τ₁.op f = 0) :
    (cohomologyPresheaf.{w, t} F (n + 1)).map d.τ₄.op e = 0 := by
  let J := SmoothSite.nisnevichTopology S
  let : Mono sq'.f₂₄ := (SmoothSite.forgetScheme S).mono_of_mono_map (by
    change Mono sq'.f₂₄.left
    infer_instance)
  let : Mono sq'.f₁₃ := hpb'.mono_f₁₃
  let q' := relativeRestriction J sq'.f₂₄ sq.f₂₄ d.τ₂ d.τ₄ d.comm₂₄ F (n + 1) q
  let := isIso_relativeRestriction_nisnevich sq' hpb' z hcomp F (n + 1)
  have hq' : q' = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (relativeRestriction J sq'.f₁₃ sq'.f₂₄
        sq'.f₁₂ sq'.f₃₄ sq'.fac.symm F (n + 1))).injective
    rw [map_zero]
    dsimp only [q']
    rw [relativeRestriction_square_naturality d, hf,
      relativeBoundary_restriction, hz, map_zero]
  exact (congrArg (fun a => (cohomologyPresheaf.{w, t} F (n + 1)).map d.τ₄.op a) hq.symm).trans
    ((relativeForget_restriction J sq'.f₂₄ sq.f₂₄ d.τ₂ d.τ₄ d.comm₂₄ F (n + 1) q).symm.trans
      ((congrArg (relativeForget J sq'.f₂₄ F (n + 1)) hq').trans (map_zero _)))

end AlgebraicGeometry.SheafCohomology
