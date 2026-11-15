/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Transfer
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenImmersion
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# Nisnevich excision for signed transfer quotients

Transfer Yoneda identifies maps from the original signed representables
with sections of an arbitrary transfer sheaf. The geometric Nisnevich
gluing theorem applies to its underlying sheaf and identifies restrictions
with precomposition by the signed graphs. The transfer representables
therefore form a pushout and their actual relative quotients are isomorphic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme Opposite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "R" => smoothTransferRepresentable k

private theorem transferSquare_isPushout_of_gluing (sq : Square Sm(k))
    (h : ∀ F : SheafWithTransfers.{u + 1} k, (sq.op.map ((toSheaf k).obj F).obj).IsPullback) :
    (sq.map (R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro F
  let P := ((toSheaf.{u + 1} k).obj F).obj
  let e (X : Sm(k)) : ((R).obj X ⟶ F) ≃ (P.obj (op X) : Type (u + 1)) :=
    (transferSectionsEquiv k (Cor.mk X) F).toEquiv
  refine (Square.IsPullback.iff_of_equiv _ _
    (e sq.X₄) (e sq.X₂) (e sq.X₃) (e sq.X₁) ?_ ?_ ?_ ?_).2
      ((h F).map (CategoryTheory.forget AddCommGrpCat.{u + 1}))
  all_goals
    funext g
    exact transferSectionsEquiv_naturality_left k F _ g

/-- The original sheafified signed representables take a Nisnevich
distinguished square to a pushout. -/
theorem transferSquare_isPushout (sq : Square Sm(k)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)] :
    (sq.map (R)).IsPushout :=
  transferSquare_isPushout_of_gluing k sq (fun F =>
    SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp ((toSheaf k).obj F))

/-- The original sheafified signed representables take an intersection
square of two open covering charts to a pushout. -/
theorem transferSquare_isPushout_of_openCover (sq : Square Sm(k)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [IsOpenImmersion sq.f₃₄.left]
    (hcover : Set.range sq.f₂₄.left ∪ Set.range sq.f₃₄.left = Set.univ) :
    (sq.map (R)).IsPushout := by
  have : Mono sq.f₂₄ := (SmoothSite.forgetScheme _).mono_of_mono_map
    (inferInstanceAs (Mono sq.f₂₄.left))
  have : Mono sq.f₃₄ := (SmoothSite.forgetScheme _).mono_of_mono_map
    (inferInstanceAs (Mono sq.f₃₄.left))
  have hc : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ SmoothSite.nisnevichTopology _ sq.X₄ := by
    apply SmoothSite.ofTwoArrows_mem_nisnevichTopology_of_field_lifting
    intro K _ x
    have hx : x (IsLocalRing.closedPoint K) ∈
        Set.range sq.f₂₄.left ∪ Set.range sq.f₃₄.left :=
      hcover.symm ▸ Set.mem_univ _
    exact hx.elim
      (fun h => Or.inl (Scheme.exists_field_lift_of_mem_range sq.f₂₄.left x h))
      (fun h => Or.inr (Scheme.exists_field_lift_of_mem_range sq.f₃₄.left x h))
  have hpb' : IsPullback sq.f₁₂.left sq.f₁₃.left sq.f₂₄.left sq.f₃₄.left :=
    (SmoothSite.forgetScheme _).map_isPullback hpb
  let : Etale sq.f₁₂.left :=
    MorphismProperty.of_isPullback hpb'.flip (inferInstance : Etale sq.f₃₄.left)
  have hdiag : Sieve.ofTwoArrows (pullback.diagonal sq.f₃₄) sq.overlapMap ∈
      SmoothSite.nisnevichTopology _ (pullback sq.f₃₄ sq.f₃₄) := by
    apply GrothendieckTopology.covering_of_eq_top
    apply Sieve.id_mem_iff_eq_top.mp
    exact ⟨_, inv (pullback.diagonal sq.f₃₄), pullback.diagonal sq.f₃₄,
      ⟨WalkingPair.left⟩, IsIso.inv_hom_id _⟩
  exact transferSquare_isPushout_of_gluing k sq (fun F =>
    sq.isPullback_op_map_of_diagonal_cover hpb hc hdiag ((toSheaf.{u + 1} k).obj F))

/-- The signed difference and sum sequence of the four transfer representables. -/
abbrev transferMayerVietorisSequence (sq : Square Sm(k)) :
    ShortComplex (SheafWithTransfers.{u + 1} k) :=
  (sq.map (R)).commSq.shortComplex

/-- The signed transfer sequence of a pushout of representables is short exact
when the right-hand arrow of the original pullback is open. -/
theorem transferMayerVietorisSequence_shortExact (sq : Square Sm(k)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] (h : (sq.map (R)).IsPushout) :
    (transferMayerVietorisSequence k sq).ShortExact := by
  have hs := (SmoothSite.forgetScheme _).map_isPullback hpb
  let : IsOpenImmersion sq.f₁₃.left :=
    MorphismProperty.of_isPullback hs (inferInstance : IsOpenImmersion sq.f₂₄.left)
  let : Mono ((R).map sq.f₁₃) := mono_transferRepresentable_map_openImmersion k sq.f₁₃
  refine { exact := h.exact_shortComplex, epi_g := h.epi_shortComplex_g, mono_f := ?_ }
  change Mono (biprod.lift ((R).map sq.f₁₂) (-((R).map sq.f₁₃)))
  have : Mono (biprod.lift ((R).map sq.f₁₂) (-((R).map sq.f₁₃)) ≫ biprod.snd) := by
    rw [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

end AlgebraicGeometry.MotivicHomotopy
