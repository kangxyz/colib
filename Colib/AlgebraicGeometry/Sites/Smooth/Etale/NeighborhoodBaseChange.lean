/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEvaluation

/-!
# Pullback on the original marked affine neighborhood values

A morphism between affine smooth objects with compatible field-valued markings induces a
contravariant map on the original neighborhood values. Its representative formula uses the
actual scheme pullback, represented by the canonical spectrum of its global sections.
The formulas for arbitrary compatible neighborhood maps imply identity, composition, and
split retraction. No extension of a presheaf to henselian schemes is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {X Y Z : SmoothSite S} [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
  {Ω : Type u} [Field Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}
  {ζ : Spec (.of Ω) ⟶ Z.left}

/-- The actual scheme pullback underlying a pulled-back affine neighborhood. -/
abbrev etaleNeighborhoodPullbackScheme (f : X ⟶ Y) (B : EtaleNeighborhood Y η) :=
  pullback f.left (etaleNeighborhoodHom Y η B).left

/-- The marked affine neighborhood obtained from the actual scheme pullback. -/
def etaleNeighborhoodPullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (B : EtaleNeighborhood Y η) : EtaleNeighborhood X ξ :=
  let P := etaleNeighborhoodPullbackScheme f B
  let p : Spec Γ(P, ⊤) ⟶ X.left := P.isoSpec.inv ≫ pullback.fst _ _
  let l : Spec (.of Ω) ⟶ Spec Γ(P, ⊤) :=
    pullback.lift ξ (etaleNeighborhoodMark Y η B)
      (h.trans (etaleNeighborhoodMark_hom Y η B).symm) ≫ P.isoSpec.hom
  (etaleNeighborhoodFiber X ξ).elementsMk (AffineEtale.mk p)
    (Over.homMk l (by
      change l ≫ p = ξ
      simp [l, p]))

/-- The original projection from the pulled-back neighborhood to the given neighborhood. -/
def etaleNeighborhoodPullbackHom (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (B : EtaleNeighborhood Y η) :
    (etaleNeighborhoodToSmooth X ξ).obj (etaleNeighborhoodPullback f h B) ⟶
      (etaleNeighborhoodToSmooth Y η).obj B :=
  homMk ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ pullback.snd _ _) (by
    change ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫
      pullback.snd f.left (etaleNeighborhoodHom Y η B).left) ≫
      ((etaleNeighborhoodHom Y η B).left ≫ Y.hom) =
      ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫
        pullback.fst f.left (etaleNeighborhoodHom Y η B).left) ≫ X.hom
    calc
      _ = (etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫
          (pullback.snd f.left (etaleNeighborhoodHom Y η B).left ≫
            (etaleNeighborhoodHom Y η B).left) ≫ Y.hom := by simp only [Category.assoc]
      _ = (etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫
          (pullback.fst f.left (etaleNeighborhoodHom Y η B).left ≫ f.left) ≫ Y.hom := by
        rw [pullback.condition]
      _ = _ := by rw [Category.assoc, MorphismProperty.Over.w f, Category.assoc])

@[reassoc (attr := simp)]
theorem etaleNeighborhoodPullbackHom_hom (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (B : EtaleNeighborhood Y η) :
    (etaleNeighborhoodPullbackHom f h B).left ≫ (etaleNeighborhoodHom Y η B).left =
      (etaleNeighborhoodHom X ξ (etaleNeighborhoodPullback f h B)).left ≫ f.left := by
  change ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ pullback.snd _ _) ≫ _ =
    ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ pullback.fst _ _) ≫ _
  simp only [Category.assoc, pullback.condition]

@[reassoc (attr := simp)]
theorem etaleNeighborhoodPullbackMark_hom (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (B : EtaleNeighborhood Y η) :
    etaleNeighborhoodMark X ξ (etaleNeighborhoodPullback f h B) ≫
      (etaleNeighborhoodPullbackHom f h B).left = etaleNeighborhoodMark Y η B := by
  change (pullback.lift ξ (etaleNeighborhoodMark Y η B) _ ≫
    (etaleNeighborhoodPullbackScheme f B).isoSpec.hom) ≫
    ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ pullback.snd _ _) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]

/-- The original neighborhood maps form the actual cartesian square. -/
theorem etaleNeighborhoodPullback_isPullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (B : EtaleNeighborhood Y η) :
    IsPullback (etaleNeighborhoodHom X ξ (etaleNeighborhoodPullback f h B)).left
      (etaleNeighborhoodPullbackHom f h B).left f.left (etaleNeighborhoodHom Y η B).left :=
  IsPullback.of_iso_pullback ⟨(etaleNeighborhoodPullbackHom_hom f h B).symm⟩
    (etaleNeighborhoodPullbackScheme f B).isoSpec.symm rfl rfl

/-- A compatible map into the given neighborhood factors through its actual pullback. -/
def etaleNeighborhoodPullbackLift (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (A : EtaleNeighborhood X ξ) (B : EtaleNeighborhood Y η)
    (g : (etaleNeighborhoodToSmooth X ξ).obj A ⟶ (etaleNeighborhoodToSmooth Y η).obj B)
    (hg : g.left ≫ (etaleNeighborhoodHom Y η B).left =
      (etaleNeighborhoodHom X ξ A).left ≫ f.left)
    (hm : etaleNeighborhoodMark X ξ A ≫ g.left = etaleNeighborhoodMark Y η B) :
    A ⟶ etaleNeighborhoodPullback f h B :=
  etaleNeighborhoodHomMk X ξ
    (pullback.lift (etaleNeighborhoodHom X ξ A).left g.left hg.symm ≫
      (etaleNeighborhoodPullbackScheme f B).isoSpec.hom)
    (by
      change (_ ≫ (etaleNeighborhoodPullbackScheme f B).isoSpec.hom) ≫
        ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ pullback.fst _ _) = _
      simp only [Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst])
    (by
      change etaleNeighborhoodMark X ξ A ≫
        (pullback.lift (etaleNeighborhoodHom X ξ A).left g.left _ ≫
          (etaleNeighborhoodPullbackScheme f B).isoSpec.hom) =
        pullback.lift ξ (etaleNeighborhoodMark Y η B) _ ≫
          (etaleNeighborhoodPullbackScheme f B).isoSpec.hom
      rw [← Category.assoc]
      apply congrArg (fun q ↦ q ≫ (etaleNeighborhoodPullbackScheme f B).isoSpec.hom)
      apply pullback.hom_ext <;> simp [hm])

@[reassoc (attr := simp)]
theorem etaleNeighborhoodPullbackLift_hom (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (A : EtaleNeighborhood X ξ) (B : EtaleNeighborhood Y η)
    (g : (etaleNeighborhoodToSmooth X ξ).obj A ⟶ (etaleNeighborhoodToSmooth Y η).obj B)
    (hg : g.left ≫ (etaleNeighborhoodHom Y η B).left =
      (etaleNeighborhoodHom X ξ A).left ≫ f.left)
    (hm : etaleNeighborhoodMark X ξ A ≫ g.left = etaleNeighborhoodMark Y η B) :
    (etaleNeighborhoodToSmooth X ξ).map (etaleNeighborhoodPullbackLift f h A B g hg hm) ≫
      etaleNeighborhoodPullbackHom f h B = g := by
  apply MorphismProperty.Over.Hom.ext
  change ((etaleNeighborhoodToSmooth X ξ).map
    (etaleNeighborhoodHomMk X ξ _ _ _)).left ≫ _ = _
  rw [etaleNeighborhoodHomMk_map_left]
  change (_ ≫ (etaleNeighborhoodPullbackScheme f B).isoSpec.hom) ≫
    ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ pullback.snd _ _) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]

variable [IsSepClosed Ω]

private theorem pullbackRepresentative_eq (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A : EtaleNeighborhood X ξ) (B : EtaleNeighborhood Y η)
    (g : (etaleNeighborhoodToSmooth X ξ).obj A ⟶ (etaleNeighborhoodToSmooth Y η).obj B)
    (hg : g.left ≫ (etaleNeighborhoodHom Y η B).left =
      (etaleNeighborhoodHom X ξ A).left ≫ f.left)
    (hm : etaleNeighborhoodMark X ξ A ≫ g.left = etaleNeighborhoodMark Y η B) :
    F.map (etaleNeighborhoodPullbackHom f h B).op ≫
        toEtaleNeighborhoodValue X ξ (etaleNeighborhoodPullback f h B) F =
      F.map g.op ≫ toEtaleNeighborhoodValue X ξ A F := by
  rw [← toEtaleNeighborhoodValue_w (f := etaleNeighborhoodPullbackLift f h A B g hg hm),
    ← Category.assoc, ← F.map_comp, ← op_comp, etaleNeighborhoodPullbackLift_hom]

/-- The cocone defining pullback on the original neighborhood value. -/
def etaleNeighborhoodPullbackCocone (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Cocone ((etaleNeighborhoodToSmooth Y η).op ⋙ F) where
  pt := etaleNeighborhoodValue X ξ F
  ι :=
    { app := fun B ↦ F.map (etaleNeighborhoodPullbackHom f h B.unop).op ≫
        toEtaleNeighborhoodValue X ξ (etaleNeighborhoodPullback f h B.unop) F
      naturality := by
        intro B C k
        dsimp
        rw [Category.comp_id, ← Category.assoc, ← F.map_comp, ← op_comp]
        exact (pullbackRepresentative_eq f h F _ _
          (etaleNeighborhoodPullbackHom f h C.unop ≫
            (etaleNeighborhoodToSmooth Y η).map k.unop)
          (by simp) (by simp)).symm }

/-- Contravariant pullback on the original marked affine neighborhood values. -/
@[colib_tag "COL-1093", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/Point/OfIsCofiltered.lean:176-187"
  "ingredient" "Actual cofiltered neighborhood presheaf-fibre colimit; the marked pullback and \
    etale-change maps are constructed here."]
def etaleNeighborhoodValuePullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValue Y η F ⟶ etaleNeighborhoodValue X ξ F :=
  (etaleNeighborhoodValueIsColimit Y η F).desc (etaleNeighborhoodPullbackCocone f h F)

/-- Pullback sends an original representative to its pullback on the actual affine fiber product. -/
@[reassoc (attr := simp)]
theorem toEtaleNeighborhoodValue_pullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : EtaleNeighborhood Y η) :
    toEtaleNeighborhoodValue Y η B F ≫ etaleNeighborhoodValuePullback f h F =
      F.map (etaleNeighborhoodPullbackHom f h B).op ≫
        toEtaleNeighborhoodValue X ξ (etaleNeighborhoodPullback f h B) F :=
  (etaleNeighborhoodValueIsColimit Y η F).fac (etaleNeighborhoodPullbackCocone f h F) (op B)

/-- The representative formula holds for every original map respecting the base and markings. -/
@[colib_tag "COL-1093", reassoc]
theorem toEtaleNeighborhoodValue_pullback_of_compatible
    (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A : EtaleNeighborhood X ξ) (B : EtaleNeighborhood Y η)
    (g : (etaleNeighborhoodToSmooth X ξ).obj A ⟶ (etaleNeighborhoodToSmooth Y η).obj B)
    (hg : g.left ≫ (etaleNeighborhoodHom Y η B).left =
      (etaleNeighborhoodHom X ξ A).left ≫ f.left)
    (hm : etaleNeighborhoodMark X ξ A ≫ g.left = etaleNeighborhoodMark Y η B) :
    toEtaleNeighborhoodValue Y η B F ≫ etaleNeighborhoodValuePullback f h F =
      F.map g.op ≫ toEtaleNeighborhoodValue X ξ A F := by
  rw [toEtaleNeighborhoodValue_pullback]
  exact pullbackRepresentative_eq f h F A B g hg hm

/-- Identity induces the identity on the actual neighborhood value. -/
@[simp]
theorem etaleNeighborhoodValuePullback_id
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValuePullback (𝟙 X) (ξ := ξ) (by simp) F = 𝟙 _ := by
  apply (etaleNeighborhoodValueIsColimit X ξ F).hom_ext
  intro A
  change toEtaleNeighborhoodValue X ξ A.unop F ≫ _ =
    toEtaleNeighborhoodValue X ξ A.unop F ≫ 𝟙 _
  rw [toEtaleNeighborhoodValue_pullback_of_compatible (A := A.unop) (g := 𝟙 _)
    (hg := by simp) (hm := by simp)]
  simp

/-- Composition is contravariant on the original marked affine neighborhood values. -/
@[colib_tag "COL-1093"]
theorem etaleNeighborhoodValuePullback_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : ξ ≫ f.left = η) (hg : η ≫ g.left = ζ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValuePullback (f ≫ g) (by
      change ξ ≫ (f.left ≫ g.left) = ζ
      rw [← Category.assoc, hf, hg]) F =
      etaleNeighborhoodValuePullback g hg F ≫ etaleNeighborhoodValuePullback f hf F := by
  apply (etaleNeighborhoodValueIsColimit Z ζ F).hom_ext
  intro C
  let B := etaleNeighborhoodPullback g hg C.unop
  let A := etaleNeighborhoodPullback f hf B
  change toEtaleNeighborhoodValue Z ζ C.unop F ≫ _ =
    toEtaleNeighborhoodValue Z ζ C.unop F ≫
      (etaleNeighborhoodValuePullback g hg F ≫ etaleNeighborhoodValuePullback f hf F)
  rw [toEtaleNeighborhoodValue_pullback_of_compatible (A := A)
    (g := etaleNeighborhoodPullbackHom f hf B ≫ etaleNeighborhoodPullbackHom g hg C.unop)
    (hg := by
      change ((etaleNeighborhoodPullbackHom f hf B).left ≫
        (etaleNeighborhoodPullbackHom g hg C.unop).left) ≫ _ =
          (etaleNeighborhoodHom X ξ A).left ≫ (f.left ≫ g.left)
      rw [Category.assoc, etaleNeighborhoodPullbackHom_hom, ← Category.assoc,
        etaleNeighborhoodPullbackHom_hom, Category.assoc])
    (hm := by
      change etaleNeighborhoodMark X ξ A ≫
        ((etaleNeighborhoodPullbackHom f hf B).left ≫
          (etaleNeighborhoodPullbackHom g hg C.unop).left) = _
      rw [← Category.assoc, etaleNeighborhoodPullbackMark_hom,
        etaleNeighborhoodPullbackMark_hom])]
  simp only [op_comp, F.map_comp, Category.assoc,
    toEtaleNeighborhoodValue_pullback, toEtaleNeighborhoodValue_pullback_assoc]
  rfl

/-- An actual marked split pair induces the normalized split pair on neighborhood values. -/
@[colib_tag "COL-1093"]
theorem etaleNeighborhoodValuePullback_retraction
    (p : X ⟶ Y) (s : Y ⟶ X) (hp : ξ ≫ p.left = η) (hs : η ≫ s.left = ξ)
    (hsp : s ≫ p = 𝟙 Y) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValuePullback p hp F ≫ etaleNeighborhoodValuePullback s hs F = 𝟙 _ := by
  rw [← etaleNeighborhoodValuePullback_comp s p hs hp]
  simpa only [hsp] using etaleNeighborhoodValuePullback_id (X := Y) (ξ := η) F

end AlgebraicGeometry.Scheme.SmoothSite
