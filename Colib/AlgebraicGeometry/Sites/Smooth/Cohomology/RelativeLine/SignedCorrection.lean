/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Basic
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SmoothSquare
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.NisnevichOverlapDifference
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic
public import Colib.CategoryTheory.Sites.Cohomology.DegreeZero

/-! # The signed relative pencil kills the original degree-one class -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {k : Type u} [Field k] {S C : Scheme.{u}}
  {X Y A : SmoothSite (Spec (.of k))}
  [IsAffine S] [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X.left ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q] (ht : q ≫ t = X.hom)
  (p : Y ⟶ X) [Etale p.left] (a : A ⟶ X) [IsOpenImmersion a.left]
  (π : C ⟶ S) (j : Y.left ⟶ C) (hq : j ≫ π = p.left ≫ q)
  (V : S.Opens) [IsAffine V.toScheme] [IsAffine (parameterOpen q ⊤ V).toScheme]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "sq" => originalSmoothSquare p a
local notation "sq'" => refinedSmoothSquare t q ht p a π j hq ⊤ V
local notation "d" => refinedSmoothSquareMap t q ht p a π j hq ⊤ V

set_option maxHeartbeats 600000 in
-- The actual refined-square and graph restrictions have different presentations.
/-- The signed correction on the full refinement kills the ordinary `H¹`
class under the literal whole-line restriction. -/
theorem degreeOne_restriction_zero_of_signed_pencil
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z]
    (s : Z ⟶ Y.left) (H : IsPullback s (𝟙 Z) p.left z)
    (hcomp : Set.range z = (Set.range a.left)ᶜ)
    {T : SmoothSite (Spec (.of k))} (g : (sq').X₁ ⟶ T) (i : T ⟶ (sq).X₁)
    (hi : g ≫ i = (d).τ₁)
    (F : SheafWithTransfers.{u + 1} k)
    (hL : PresheafWithTransfers.HasRestrictionDifferenceLifting F.obj g (sq').f₁₂ (sq').f₁₃)
    (e : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).obj (op X))
    (hA : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map a.op e = 0)
    (hY : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op e = 0) :
    (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map
      (SmoothSite.openInclusion X (parameterOpen q ⊤ V)).op e = 0 := by
  let keep : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ (⊤ : X.left.Opens) := fun _ _ => trivial
  let z' := markToParameter q ⊤ V z keep
  have hs : s ≫ p.left = z := H.w.trans (Category.id_comp z)
  have H' := closedLift_isPullback q ⊤ V z keep p.left s hs H
  let : IsClosedImmersion z' := MorphismProperty.of_isPullback
    (markToParameter_isPullback q ⊤ V z keep).flip inferInstance
  let : IsOpenImmersion (sq).f₂₄.left := inferInstanceAs (IsOpenImmersion a.left)
  let : Etale (sq).f₃₄.left := inferInstanceAs (Etale p.left)
  let : IsOpenImmersion (sq').f₂₄.left := inferInstanceAs (IsOpenImmersion (secondMap q ⊤ V a.left))
  let : Etale (sq').f₃₄.left := inferInstanceAs (Etale (firstMap q ⊤ V p.left))
  let : IsIso (pullback.snd (sq).f₃₄.left z) := by
    change IsIso (pullback.snd p.left z)
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let : IsIso (pullback.snd (sq').f₃₄.left z') := by
    change IsIso (pullback.snd (firstMap q ⊤ V p.left) z')
    rw [← H'.isoPullback_inv_snd]
    infer_instance
  have hz : Set.range z' = (Set.range (sq').f₂₄.left)ᶜ := by
    change Set.range z' = (Set.range (secondMap q ⊤ V a.left))ᶜ
    rw [SmoothSite.range_fst_of_cartesian (markToParameter_isPullback q ⊤ V z keep), hcomp,
      Set.preimage_compl, ← Scheme.Pullback.range_snd]
  let G := (SheafWithTransfers.toSheaf k).obj F
  refine SheafCohomology.ordinary_eq_zero_of_overlap_difference d
    (originalSmoothSquare_isPullback p a) (refinedSmoothSquare_isPullback t q ht p a π j hq ⊤ V)
    z z' hcomp hz G 0 ?_ e hA hY
  dsimp only
  intro f
  let s₀ := extSectionsAddEquiv.{w, u + 1} (sq).X₁ G f
  let s₁ := G.obj.map i.op s₀
  obtain ⟨b, c, hbc⟩ := hL s₁
  refine ⟨(extSectionsAddEquiv.{w, u + 1} (sq').X₂ G).symm b,
    (extSectionsAddEquiv.{w, u + 1} (sq').X₃ G).symm c, ?_⟩
  apply (extSectionsAddEquiv.{w, u + 1} (sq').X₁ G).injective
  have hNat {J K : SmoothSite (Spec (.of k))} (j : J ⟶ K)
      (x : (cohomologyPresheaf.{w, u + 1} G 0).obj (op K)) :
      extSectionsAddEquiv.{w, u + 1} J G ((cohomologyPresheaf.{w, u + 1} G 0).map j.op x) =
        G.obj.map j.op (extSectionsAddEquiv.{w, u + 1} K G x) :=
    extSectionsAddEquiv_naturality_left j G x
  rw [map_sub, hNat (sq').f₁₂, hNat (sq').f₁₃, hNat (d).τ₁,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  change G.obj.map (sq').f₁₂.op b - G.obj.map (sq').f₁₃.op c = G.obj.map (d).τ₁.op s₀
  change G.obj.map (sq').f₁₂.op b - G.obj.map (sq').f₁₃.op c = G.obj.map g.op s₁ at hbc
  exact hbc.trans (by
    dsimp only [s₁]
    rw [← Functor.map_comp_apply, ← op_comp, hi])

include ht in
/-- The whole-pencil lifting kills the degree-one class along its actual refined site maps. -/
theorem degreeOne_restriction_zero_of_refined_lifting
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z]
    (s : Z ⟶ Y.left) (H : IsPullback s (𝟙 Z) p.left z)
    (hcomp : Set.range z = (Set.range a.left)ᶜ)
    {T : SmoothSite (Spec (.of k))}
    (g : refinedOverlapSite t q ⊤ V π j p.left hq a.left ⟶ T)
    (i : T ⟶ SmoothSite.etalePullback p a)
    (hi : g.left ≫ i.left = overlapToOriginal q ⊤ V p.left a.left)
    (F : SheafWithTransfers.{u + 1} k)
    (hL : PresheafWithTransfers.HasRestrictionDifferenceLifting F.obj g
      (refinedBeta t q ⊤ V π j p.left hq a.left) (refinedAlpha t q ⊤ V π j p.left hq a.left))
    (e : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).obj (op X))
    (hA : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map a.op e = 0)
    (hY : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op e = 0) :
    (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map
      (SmoothSite.openInclusion X (parameterOpen q ⊤ V)).op e = 0 := by
  have hi' : (g ≫ i : (sq').X₁ ⟶ (sq).X₁) = (d).τ₁ := MorphismProperty.Over.Hom.ext hi
  exact degreeOne_restriction_zero_of_signed_pencil (k := k) t q ht p a π j hq V
    z s H hcomp g i hi' F hL e hA hY

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
