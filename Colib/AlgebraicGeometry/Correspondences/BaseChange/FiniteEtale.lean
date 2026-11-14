/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.FiniteEtaleSupport
public import Colib.AlgebraicGeometry.Correspondences.BaseChange.RelativeHomEquiv
public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange
public import Colib.Util.References

/-! # Finite étale base change of finite correspondences

For a base map `r : T ⟶ S` the product of the two base-changed schemes over
`T` is the pullback of the original product along `X ×_S T ⟶ X`. This
identifies the ambient finite étale cover and its coefficientwise descent
for the base change in Riou, *Opérations de Steenrod motiviques*,
arXiv:1207.3121v1, Definition 2.1.3, maps (2) and (4).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace Stacks.Chow

variable {S T : Scheme.{u}} (r : T ⟶ S) (X Y : SmoothSite S)

local notation "fₜ" => pullback.snd X.hom r
local notation "gₜ" => pullback.snd Y.hom r

/-- The product after base change is the source pullback of the original product. -/
def baseChangeCorrespondenceProductIso :
    pullback fₜ gₜ ≅ pullback (pullback.fst X.hom r) (pullback.fst X.hom Y.hom) :=
  relativeCorrespondenceProductIso r fₜ Y.hom ≪≫
    pullback.congrHom (pullback.condition (f := X.hom) (g := r)).symm rfl ≪≫
    (pullbackRightPullbackFstIso X.hom Y.hom (pullback.fst X.hom r)).symm

/-- The map to the original ambient product along the base change. -/
def baseChangeCorrespondenceProductMap :
    pullback fₜ gₜ ⟶ pullback X.hom Y.hom :=
  (baseChangeCorrespondenceProductIso r X Y).hom ≫ pullback.snd _ _

@[reassoc (attr := simp)]
theorem baseChangeCorrespondenceProductMap_snd :
    baseChangeCorrespondenceProductMap r X Y ≫ pullback.snd X.hom Y.hom =
      pullback.snd fₜ gₜ ≫ pullback.fst Y.hom r := by
  simp only [baseChangeCorrespondenceProductMap, baseChangeCorrespondenceProductIso,
    Iso.trans_hom, Category.assoc, Iso.symm_hom, pullbackRightPullbackFstIso_inv_snd_snd,
    pullback.congrHom, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    relativeCorrespondenceProductIso_hom_snd]

/-- The ambient base change is Cartesian over the projection to the original source. -/
theorem baseChangeCorrespondenceProductMap_isPullback :
    IsPullback (baseChangeCorrespondenceProductMap r X Y) (pullback.fst fₜ gₜ)
      (pullback.fst X.hom Y.hom) (pullback.fst X.hom r) := by
  have hfst : (baseChangeCorrespondenceProductIso r X Y).hom ≫ pullback.fst _ _ =
      pullback.fst fₜ gₜ := by
    simp only [baseChangeCorrespondenceProductIso, Iso.trans_hom, Category.assoc, Iso.symm_hom,
      pullbackRightPullbackFstIso_inv_fst, pullback.congrHom, asIso_hom, pullback.map,
      pullback.lift_fst, Category.comp_id, relativeCorrespondenceProductIso_hom_fst]
  exact (IsPullback.of_hasPullback _ _).flip.of_iso'
    (baseChangeCorrespondenceProductIso r X Y) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [baseChangeCorrespondenceProductMap]) (by simpa using hfst) (by simp) (by simp)

instance [IsFinite r] : IsFinite (baseChangeCorrespondenceProductMap r X Y) :=
  MorphismProperty.of_isPullback (baseChangeCorrespondenceProductMap_isPullback r X Y).flip
    (inferInstance : IsFinite (pullback.fst X.hom r))

instance [Etale r] : Etale (baseChangeCorrespondenceProductMap r X Y) :=
  MorphismProperty.of_isPullback (baseChangeCorrespondenceProductMap_isPullback r X Y).flip
    (inferInstance : Etale (pullback.fst X.hom r))

/-- Pullback of signed native finite correspondences along a finite étale base map. -/
def finiteEtaleBaseChangeCorrespondences [IsFinite r] [Etale r] :
    finiteCorrespondences X.hom Y.hom →+ finiteCorrespondences fₜ gₜ :=
  finiteCorrespondencesEtalePullback (baseChangeCorrespondenceProductMap_isPullback r X Y)

@[simp]
theorem finiteEtaleBaseChangeCorrespondences_apply [IsFinite r] [Etale r]
    (c : finiteCorrespondences X.hom Y.hom) (z : (pullback fₜ gₜ : Scheme.{u})) :
    (finiteEtaleBaseChangeCorrespondences r X Y c).val z =
      c.val (baseChangeCorrespondenceProductMap r X Y z) := rfl

/-- Native finite correspondences descend along a finite étale surjective base map
exactly when their two ambient cycle restrictions agree. -/
theorem existsUnique_finiteEtaleBaseChangeCorrespondences [IsFinite r] [Etale r] [Surjective r]
    (c : finiteCorrespondences fₜ gₜ) :
    (∃! d : finiteCorrespondences X.hom Y.hom,
        finiteEtaleBaseChangeCorrespondences r X Y d = c) ↔
      finiteEtaleCyclePullback
          (pullback.fst (baseChangeCorrespondenceProductMap r X Y)
            (baseChangeCorrespondenceProductMap r X Y)) c.val =
        finiteEtaleCyclePullback
          (pullback.snd (baseChangeCorrespondenceProductMap r X Y)
            (baseChangeCorrespondenceProductMap r X Y)) c.val :=
  existsUnique_finiteCorrespondencesEtalePullback
    (baseChangeCorrespondenceProductMap_isPullback r X Y) c

end Stacks.Chow

attribute [colib_tag "COL-1232"]
  Stacks.Chow.baseChangeCorrespondenceProductMap_isPullback
  Stacks.Chow.finiteEtaleBaseChangeCorrespondences
  Stacks.Chow.finiteEtaleBaseChangeCorrespondences_apply
  Stacks.Chow.existsUnique_finiteEtaleBaseChangeCorrespondences

attribute [colib_ref "Riou2012Steenrod" "Section 2.1, Definition 2.1.3, maps (2) and (4), p. 15"
  "ingredient" "Finite étale pullback and descent of the integral finite correspondences"]
  Stacks.Chow.existsUnique_finiteEtaleBaseChangeCorrespondences
