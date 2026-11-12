/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.MarkedBaseChange
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitNeighborhoods
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodBaseChange

/-!
# The actual affine marked pullback functor

The original chosen affine pullbacks compare to native small étale base change,
with their actual markings. Initiality and colimit transport follow from this comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [IsAffine S]
  {X Y : SmoothSite S} [IsAffine X.left] [IsAffine Y.left]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}

omit [IsAffine X.left] [IsSepClosed Ω] in
/-- Faithfulness of the actual neighborhood scheme maps. -/
theorem etaleNeighborhood_hom_ext {A B : EtaleNeighborhood X ξ} (a b : A ⟶ B)
    (h : ((etaleNeighborhoodToSmooth X ξ).map a).left =
      ((etaleNeighborhoodToSmooth X ξ).map b).left) : a = b := by
  apply Functor.Elements.hom_ext
  apply (AffineEtale.Spec X.left).map_injective
  exact MorphismProperty.Over.Hom.ext h

omit [IsSepClosed Ω] in
/-- A map into the original pullback is determined by its actual projection. -/
theorem etaleNeighborhoodPullback_hom_ext (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    {A : EtaleNeighborhood X ξ} {B : EtaleNeighborhood Y η}
    (a b : A ⟶ etaleNeighborhoodPullback f h B)
    (hab : (etaleNeighborhoodToSmooth X ξ).map a ≫ etaleNeighborhoodPullbackHom f h B =
      (etaleNeighborhoodToSmooth X ξ).map b ≫ etaleNeighborhoodPullbackHom f h B) : a = b := by
  apply etaleNeighborhood_hom_ext
  apply (etaleNeighborhoodPullback_isPullback f h B).hom_ext
  · simp
  · exact congrArg (fun g ↦ g.left) hab

/-- The original chosen affine pullback, made functorial by its actual universal property. -/
def etaleNeighborhoodPullbackFunctor (f : X ⟶ Y) (h : ξ ≫ f.left = η) :
    EtaleNeighborhood Y η ⥤ EtaleNeighborhood X ξ where
  obj B := etaleNeighborhoodPullback f h B
  map {A B} g := etaleNeighborhoodPullbackLift f h _ B
    (etaleNeighborhoodPullbackHom f h A ≫ (etaleNeighborhoodToSmooth Y η).map g)
    (by simp) (by simp)
  map_id A := by
    apply etaleNeighborhoodPullback_hom_ext f h
    simp
  map_comp a b := by
    apply etaleNeighborhoodPullback_hom_ext f h
    simp

omit [IsSepClosed Ω] in
@[reassoc (attr := simp)]
theorem etaleNeighborhoodPullbackFunctor_map_hom (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    {A B : EtaleNeighborhood Y η} (g : A ⟶ B) :
    (etaleNeighborhoodToSmooth X ξ).map ((etaleNeighborhoodPullbackFunctor f h).map g) ≫
      etaleNeighborhoodPullbackHom f h B =
    etaleNeighborhoodPullbackHom f h A ≫ (etaleNeighborhoodToSmooth Y η).map g :=
  etaleNeighborhoodPullbackLift_hom f h _ _ _ (by simp [etaleNeighborhoodPullbackFunctor])
    (by simp [etaleNeighborhoodPullbackFunctor])

/-- The actual affine pullback and native marked base change have the same marked scheme. -/
def etaleNeighborhoodPullbackSmallIso (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (B : EtaleNeighborhood Y η) :
    (affineNeighborhoodToSmallPoint X ξ).obj (etaleNeighborhoodPullback f h B) ≅
      (markedEtaleBaseChange f.left ξ η h).obj ((affineNeighborhoodToSmallPoint Y η).obj B) :=
  Functor.Elements.isoMk
    (MorphismProperty.Over.isoMk
      ((etaleNeighborhoodPullbackScheme f B).isoSpec.symm ≪≫
        pullbackSymmetry f.left (etaleNeighborhoodHom Y η B).left)
      (by
        change (_ ≫ (pullbackSymmetry _ _).hom) ≫ pullback.snd _ _ = _ ≫ pullback.fst _ _
        simp))
    (by
      apply Over.OverMorphism.ext
      change (pullback.lift ξ (etaleNeighborhoodMark Y η B) _ ≫
        (etaleNeighborhoodPullbackScheme f B).isoSpec.hom) ≫
        ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ (pullbackSymmetry _ _).hom) =
        pullback.lift (etaleNeighborhoodMark Y η B) ξ _
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      apply pullback.hom_ext <;> simp)

/-- Comparison of the original affine marked pullback functor with native marked base change. -/
def etaleNeighborhoodPullbackSmallNatIso (f : X ⟶ Y) (h : ξ ≫ f.left = η) :
    etaleNeighborhoodPullbackFunctor f h ⋙ affineNeighborhoodToSmallPoint X ξ ≅
      affineNeighborhoodToSmallPoint Y η ⋙ markedEtaleBaseChange f.left ξ η h :=
  NatIso.ofComponents (etaleNeighborhoodPullbackSmallIso f h) (by
    intro A B g
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change ((etaleNeighborhoodToSmooth X ξ).map
      ((etaleNeighborhoodPullbackFunctor f h).map g)).left ≫
      ((etaleNeighborhoodPullbackScheme f B).isoSpec.inv ≫ (pullbackSymmetry _ _).hom) =
      ((etaleNeighborhoodPullbackScheme f A).isoSpec.inv ≫ (pullbackSymmetry _ _).hom) ≫
      ((smallEtaleBaseChange f.left).map ((AffineEtale.Spec Y.left).map g.hom)).left
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
      erw [smallEtaleBaseChange_map_fst]
      erw [pullbackSymmetry_hom_comp_fst_assoc]
      exact congrArg (fun a ↦ a.left) (etaleNeighborhoodPullbackFunctor_map_hom f h g)
    · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
      erw [smallEtaleBaseChange_map_snd]
      erw [pullbackSymmetry_hom_comp_snd]
      exact etaleNeighborhoodMap_hom X ξ ((etaleNeighborhoodPullbackFunctor f h).map g))

private def affineNeighborhoodToSmallPointFullyFaithful :
    (affineNeighborhoodToSmallPoint X ξ).FullyFaithful where
  preimage f := Functor.Elements.homMk ((AffineEtale.Spec X.left).preimage f.hom) (by
    change (pointSmallEtale ξ).fiber.map
      ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom)) _ = _
    rw [Functor.map_preimage]
    exact f.map_val)
  map_preimage f := Functor.Elements.hom_ext ((AffineEtale.Spec X.left).map_preimage f.hom)
  preimage_map f := Functor.Elements.hom_ext (Functor.preimage_map f.hom)

/-- The original affine neighborhood pullback is initial when native small-site pullback
is an equivalence. Both original markings are retained. -/
theorem etaleNeighborhoodPullbackFunctor_initial (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    [(smallEtaleBaseChange f.left).IsEquivalence] :
    (etaleNeighborhoodPullbackFunctor f h).Initial := by
  have := markedEtaleBaseChange_isEquivalence f.left ξ η h
  let ff := affineNeighborhoodToSmallPointFullyFaithful (X := X) (ξ := ξ)
  let := ff.full
  let := ff.faithful
  have : (etaleNeighborhoodPullbackFunctor f h ⋙ affineNeighborhoodToSmallPoint X ξ).Initial :=
    Functor.initial_of_natIso (etaleNeighborhoodPullbackSmallNatIso f h).symm
  exact Functor.initial_of_comp_full_faithful _ (affineNeighborhoodToSmallPoint X ξ)

/-- Original presheaf restriction along every actual pullback projection. -/
def etaleNeighborhoodPullbackDiagramMap (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleNeighborhoodToSmooth Y η).op ⋙ P ⟶
      (etaleNeighborhoodPullbackFunctor f h).op ⋙ (etaleNeighborhoodToSmooth X ξ).op ⋙ P where
  app B := P.map (etaleNeighborhoodPullbackHom f h B.unop).op
  naturality A B g := by
    dsimp
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
      etaleNeighborhoodPullbackFunctor_map_hom]

/-- The colimit comparison supplied by actual cofinal base change and invertible
original projection restrictions. -/
def etaleNeighborhoodPullbackIso (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [(smallEtaleBaseChange f.left).IsEquivalence]
    [∀ B : EtaleNeighborhood Y η, IsIso (P.map (etaleNeighborhoodPullbackHom f h B).op)] :
    etaleNeighborhoodValue Y η P ≅ etaleNeighborhoodValue X ξ P := by
  let := etaleNeighborhoodInitiallySmall.{u, u + 1} X ξ
  let := etaleNeighborhoodInitiallySmall.{u, u + 1} Y η
  have := etaleNeighborhoodPullbackFunctor_initial f h
  have : ∀ B, IsIso ((etaleNeighborhoodPullbackDiagramMap f h P).app B) := fun B ↦
    inferInstanceAs (IsIso (P.map (etaleNeighborhoodPullbackHom f h B.unop).op))
  have : IsIso (etaleNeighborhoodPullbackDiagramMap f h P) :=
    NatIso.isIso_of_isIso_app _
  exact (etaleNeighborhoodColimitIso Y η P).symm ≪≫
    HasColimit.isoOfNatIso (asIso (etaleNeighborhoodPullbackDiagramMap f h P)) ≪≫
    Functor.Final.colimitIso (etaleNeighborhoodPullbackFunctor f h).op
      ((etaleNeighborhoodToSmooth X ξ).op ⋙ P) ≪≫ etaleNeighborhoodColimitIso X ξ P

/-- The cofinal colimit isomorphism is exactly COL1093's original marked pullback. -/
theorem etaleNeighborhoodPullbackIso_hom (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [(smallEtaleBaseChange f.left).IsEquivalence]
    [∀ B : EtaleNeighborhood Y η, IsIso (P.map (etaleNeighborhoodPullbackHom f h B).op)] :
    (etaleNeighborhoodPullbackIso f h P).hom = etaleNeighborhoodValuePullback f h P := by
  let := etaleNeighborhoodInitiallySmall.{u, u + 1} X ξ
  let := etaleNeighborhoodInitiallySmall.{u, u + 1} Y η
  apply (etaleNeighborhoodValueIsColimit Y η P).hom_ext
  intro B
  change toEtaleNeighborhoodValue Y η B.unop P ≫ _ =
    toEtaleNeighborhoodValue Y η B.unop P ≫ _
  rw [toEtaleNeighborhoodValue_pullback,
    ← colimit_ι_etaleNeighborhoodColimitIso_hom Y η P B.unop]
  simp only [etaleNeighborhoodPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, HasColimit.ι_isoOfNatIso_hom_assoc,
    Functor.Final.ι_colimitIso_hom_assoc]
  exact congrArg (fun g ↦ P.map (etaleNeighborhoodPullbackHom f h B.unop).op ≫ g)
    (colimit_ι_etaleNeighborhoodColimitIso_hom X ξ P
      (etaleNeighborhoodPullback f h B.unop))

/-- Actual cofinal base change and original stage restrictions make the original
marked neighborhood pullback invertible. -/
theorem isIso_etaleNeighborhoodValuePullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [(smallEtaleBaseChange f.left).IsEquivalence]
    [∀ B : EtaleNeighborhood Y η, IsIso (P.map (etaleNeighborhoodPullbackHom f h B).op)] :
    IsIso (etaleNeighborhoodValuePullback f h P) := by
  rw [← etaleNeighborhoodPullbackIso_hom f h P]
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
