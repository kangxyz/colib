/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FixedTargetGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.Diagram

/-! # The simultaneous first correction is a literal original affine open

The open-image isomorphism remembers the original target map. Each source is
its actual Cartesian pullback, so a later whole-zero base restriction uses the
same source and marking rather than choosing an unrelated étale neighborhood.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A Z : Scheme.{u}}
  {b : X ⟶ Spec (.of k)} {p : Y ⟶ X} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {x : X}
  (e : OriginalEtalePresentation k b p a z s x)
  (U : e.target.Opens) (V : (Spec e.base).Opens)

/-- The simultaneous parameter-and-base open maps to the unchanged original target. -/
abbrev retainedToOriginal := (parameterOpen e.curveProjection U V).ι ≫ e.refinement
/-- Its actual open image in the original target. -/
abbrev retainedOriginalOpen : X.Opens := (retainedToOriginal e U V).opensRange

/-- The first correction really is an affine original open. -/
theorem retainedOriginalOpen_affine
    [IsAffine (parameterOpen e.curveProjection U V).toScheme] :
    IsAffineOpen (retainedOriginalOpen e U V) :=
  isAffineOpen_opensRange (retainedToOriginal e U V)

/-- The original selected point survives both restrictions. -/
theorem point_mem_retainedOriginalOpen (hU : e.point ∈ U)
    (hV : e.curveProjection e.point ∈ V) : x ∈ retainedOriginalOpen e U V :=
  ⟨⟨e.point, hU, hV⟩, e.point_eq⟩

/-- The canonical, map-preserving open-image identification. -/
def retainedOriginalOpenIso : (parameterOpen e.curveProjection U V).toScheme ≅
    (retainedOriginalOpen e U V).toScheme := (retainedToOriginal e U V).isoOpensRange

@[reassoc (attr := simp)] theorem retainedOriginalOpenIso_hom_ι :
    (retainedOriginalOpenIso e U V).hom ≫ (retainedOriginalOpen e U V).ι =
      retainedToOriginal e U V := Scheme.Hom.isoOpensRange_hom_ι _

@[reassoc (attr := simp)] theorem retainedOriginalOpenIso_inv_original :
    (retainedOriginalOpenIso e U V).inv ≫ retainedToOriginal e U V =
      (retainedOriginalOpen e U V).ι := Scheme.Hom.isoOpensRange_inv_comp _

/-- Both successive target restrictions are literally Cartesian over the original arrow. -/
theorem retainedOriginalPullback_isPullback {Q : Scheme.{u}} (t : Q ⟶ X) :
    IsPullback
      (pullback.snd (pullback.snd t e.refinement) (parameterOpen e.curveProjection U V).ι ≫
        (retainedOriginalOpenIso e U V).hom)
      (pullback.fst (pullback.snd t e.refinement) (parameterOpen e.curveProjection U V).ι ≫
        pullback.fst t e.refinement)
      (retainedOriginalOpen e U V).ι t := by
  have H := (IsPullback.of_hasPullback (pullback.snd t e.refinement)
    (parameterOpen e.curveProjection U V).ι).flip.paste_vert
      (IsPullback.of_hasPullback t e.refinement).flip
  apply H.of_iso (Iso.refl _) (retainedOriginalOpenIso e U V) (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp

/-- The canonical identification with the original-arrow pullback. -/
def retainedOriginalPullbackIso {Q : Scheme.{u}} (t : Q ⟶ X) :
    pullback (pullback.snd t e.refinement) (parameterOpen e.curveProjection U V).ι ≅
      pullback (retainedOriginalOpen e U V).ι t :=
  (retainedOriginalPullback_isPullback e U V t).isoPullback

@[reassoc (attr := simp)] theorem retainedOriginalPullbackIso_hom_fst
    {Q : Scheme.{u}} (t : Q ⟶ X) :
    (retainedOriginalPullbackIso e U V t).hom ≫
        pullback.fst (retainedOriginalOpen e U V).ι t =
      pullback.snd (pullback.snd t e.refinement) (parameterOpen e.curveProjection U V).ι ≫
        (retainedOriginalOpenIso e U V).hom :=
  (retainedOriginalPullback_isPullback e U V t).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem retainedOriginalPullbackIso_hom_snd
    {Q : Scheme.{u}} (t : Q ⟶ X) :
    (retainedOriginalPullbackIso e U V t).hom ≫
        pullback.snd (retainedOriginalOpen e U V).ι t =
      pullback.fst (pullback.snd t e.refinement) (parameterOpen e.curveProjection U V).ι ≫
        pullback.fst t e.refinement :=
  (retainedOriginalPullback_isPullback e U V t).isoPullback_hom_snd

/-- In particular the puncture is its exact intersection with the retained original open. -/
def retainedOriginalPunctureIso (D : X.Opens) :
    pullback (pullback.snd D.ι e.refinement) (parameterOpen e.curveProjection U V).ι ≅
      (retainedOriginalOpen e U V ⊓ D).toScheme :=
  retainedOriginalPullbackIso e U V D.ι ≪≫
    (isPullback_opens_inf (retainedOriginalOpen e U V) D).isoPullback.symm

@[reassoc (attr := simp)] theorem retainedOriginalPunctureIso_hom_left (D : X.Opens) :
    (retainedOriginalPunctureIso e U V D).hom ≫ X.homOfLE inf_le_left =
      pullback.snd (pullback.snd D.ι e.refinement) (parameterOpen e.curveProjection U V).ι ≫
        (retainedOriginalOpenIso e U V).hom := by
  simp [retainedOriginalPunctureIso, Category.assoc]

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
