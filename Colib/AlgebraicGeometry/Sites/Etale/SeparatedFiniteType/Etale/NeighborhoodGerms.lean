/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Topology
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEvaluation

/-!
# Germs into small étale targets and lifts of the base marking

For the actual small-base-site inclusion into the smooth site, a germ of a map
from a marked smooth neighborhood to an étale base object determines a lift of
the composite marking to that target. Actual pullback supplies every such lift,
and the étale diagonal supplies uniqueness after an original marked refinement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S : Scheme.{u}} [IsAffine S] (Y : SmoothSite S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ Y.left)

omit [IsSepClosed Ω] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A map into an actual small-base object retains its original map over the base. -/
@[reassoc]
theorem toSmoothSite_base_map_over (U : EtaleSeparatedFiniteType S)
    (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    f.left ≫ U.hom = (SmoothSite.etaleNeighborhoodHom Y ξ A).left ≫ Y.hom := by
  have h := MorphismProperty.Over.w f
  change f.left ≫ (U.hom ≫ 𝟙 S) =
    (SmoothSite.etaleNeighborhoodHom Y ξ A).left ≫ Y.hom at h
  erw [Category.comp_id] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a representative scheme map to the original marking gives the native
small-site lift of the composite base marking. -/
def etaleNeighborhoodMapLift (U : EtaleSeparatedFiniteType S)
    (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    (pointSmallEtale (ξ ≫ Y.hom)).fiber.obj ((toSmallEtale S).obj U) :=
  Over.homMk (SmoothSite.etaleNeighborhoodMark Y ξ A ≫ f.left) (by
    change (SmoothSite.etaleNeighborhoodMark Y ξ A ≫ f.left) ≫ U.hom = ξ ≫ Y.hom
    rw [Category.assoc, toSmoothSite_base_map_over, ← Category.assoc,
      SmoothSite.etaleNeighborhoodMark_hom])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each native small-site lift is represented by an original affine marked smooth
neighborhood, constructed from the actual scheme pullback. -/
theorem exists_etaleNeighborhood_mapLift (U : EtaleSeparatedFiniteType S)
    (z : (pointSmallEtale (ξ ≫ Y.hom)).fiber.obj ((toSmallEtale S).obj U)) :
    ∃ (A : SmoothSite.EtaleNeighborhood Y ξ)
      (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
        (toSmoothSite (SmoothSite.base S)).obj U),
      etaleNeighborhoodMapLift Y ξ U A f = z := by
  let p : pullback Y.hom U.hom ⟶ Y.left := pullback.fst _ _
  let l : Spec (.of Ω) ⟶ pullback Y.hom U.hom :=
    pullback.lift ξ z.left (Over.w z).symm
  obtain ⟨A, g, hg, hm⟩ := SmoothSite.exists_etaleNeighborhood_refinement Y ξ p l
    (pullback.lift_fst _ _ _)
  let f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U :=
    SmoothSite.homMk (g ≫ pullback.snd _ _) (by
      change (g ≫ pullback.snd Y.hom U.hom) ≫ (U.hom ≫ 𝟙 S) =
        (SmoothSite.etaleNeighborhoodHom Y ξ A).left ≫ Y.hom
      erw [Category.comp_id, Category.assoc, ← pullback.condition, ← Category.assoc, hg])
  refine ⟨A, f, ?_⟩
  apply Over.OverMorphism.ext
  change SmoothSite.etaleNeighborhoodMark Y ξ A ≫ (g ≫ pullback.snd _ _) = z.left
  rw [← Category.assoc, hm]
  exact pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Two maps into an actual étale base target inducing the same lift agree after an
original marked affine refinement. The refinement is pulled back from the étale diagonal. -/
@[colib_ref "mathlib_stable_localization_pin"
  "Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:122-146"
  "ingredient" "The etale diagonal is an open immersion, giving a marked equality refinement"]
theorem exists_etaleNeighborhood_refinement_eq_of_mapLift_eq
    (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f g : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U)
    (h : etaleNeighborhoodMapLift Y ξ U A f = etaleNeighborhoodMapLift Y ξ U A g) :
    ∃ (B : SmoothSite.EtaleNeighborhood Y ξ) (q : B ⟶ A),
      (SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q ≫ f =
        (SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q ≫ g := by
  have hm : SmoothSite.etaleNeighborhoodMark Y ξ A ≫ f.left =
      SmoothSite.etaleNeighborhoodMark Y ξ A ≫ g.left := congrArg (fun z ↦ z.left) h
  let a : ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A).left ⟶
      pullback U.hom U.hom :=
    pullback.lift f.left g.left ((toSmoothSite_base_map_over Y ξ U A f).trans
      (toSmoothSite_base_map_over Y ξ U A g).symm)
  let P := pullback a (pullback.diagonal U.hom)
  let p : P ⟶ ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A).left := pullback.fst _ _
  let l : Spec (.of Ω) ⟶ P :=
    pullback.lift (SmoothSite.etaleNeighborhoodMark Y ξ A)
      (SmoothSite.etaleNeighborhoodMark Y ξ A ≫ f.left) (by
        apply pullback.hom_ext <;> simp [a, hm])
  let b := p ≫ (SmoothSite.etaleNeighborhoodHom Y ξ A).left
  obtain ⟨B, j, hj, hmark⟩ := SmoothSite.exists_etaleNeighborhood_refinement Y ξ b l (by
    change (l ≫ p) ≫ (SmoothSite.etaleNeighborhoodHom Y ξ A).left = ξ
    rw [pullback.lift_fst]
    exact SmoothSite.etaleNeighborhoodMark_hom Y ξ A)
  let q : B ⟶ A := SmoothSite.etaleNeighborhoodHomMk Y ξ (j ≫ p) hj (by
    rw [← Category.assoc, hmark]
    exact pullback.lift_fst _ _ _)
  refine ⟨B, q, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  change ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q).left ≫ f.left =
    ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q).left ≫ g.left
  dsimp only [q]
  rw [SmoothSite.etaleNeighborhoodHomMk_map_left]
  have hp : p ≫ f.left = p ≫ g.left := by
    have hfst := congrArg (fun t ↦ t ≫ pullback.fst U.hom U.hom)
      (pullback.condition (f := a) (g := pullback.diagonal U.hom))
    have hsnd := congrArg (fun t ↦ t ≫ pullback.snd U.hom U.hom)
      (pullback.condition (f := a) (g := pullback.diagonal U.hom))
    simp only [a, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
      Category.comp_id] at hfst
    simp only [a, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
      Category.comp_id] at hsnd
    exact hfst.trans hsnd.symm
  simpa only [Category.assoc] using congrArg (fun t ↦ j ≫ t) hp

/-- Refinement does not change the native lift represented by a scheme map. -/
@[simp]
theorem etaleNeighborhoodMapLift_refinement (U : EtaleSeparatedFiniteType S)
    {A B : SmoothSite.EtaleNeighborhood Y ξ} (q : A ⟶ B)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj B ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    etaleNeighborhoodMapLift Y ξ U A ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q ≫ f) =
      etaleNeighborhoodMapLift Y ξ U B f := by
  apply Over.OverMorphism.ext
  change SmoothSite.etaleNeighborhoodMark Y ξ A ≫
    (((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q).left ≫ f.left) = _
  rw [← Category.assoc, SmoothSite.etaleNeighborhoodMark_map]
  rfl

local instance : InitiallySmall.{u + 1} (SmoothSite.EtaleNeighborhood Y ξ) :=
  SmoothSite.etaleNeighborhoodInitiallySmall.{u, u + 1} Y ξ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on the original marking is a cocone on the actual diagram of scheme maps. -/
def etaleNeighborhoodLiftCocone (U : EtaleSeparatedFiniteType S) :
    Cocone ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).op ⋙
      shrinkYoneda.{u + 1}.obj ((toSmoothSite (SmoothSite.base S)).obj U)) where
  pt := ULift.{u + 1} ((pointSmallEtale (ξ ≫ Y.hom)).fiber.obj ((toSmallEtale S).obj U))
  ι :=
    { app := fun A ↦ ↾fun f ↦ ULift.up
        (etaleNeighborhoodMapLift Y ξ U A.unop (shrinkYonedaObjObjEquiv.{u + 1} f))
      naturality := by
        intro A B q
        ext f
        obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.{u + 1}.symm.surjective f
        change ULift.up (etaleNeighborhoodMapLift Y ξ U B.unop
          (shrinkYonedaObjObjEquiv.{u + 1} ((shrinkYoneda.{u + 1}.obj
            ((toSmoothSite (SmoothSite.base S)).obj U)).map
              ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q.unop).op
                (shrinkYonedaObjObjEquiv.{u + 1}.symm f)))) =
          ULift.up (etaleNeighborhoodMapLift Y ξ U A.unop
            (shrinkYonedaObjObjEquiv.{u + 1} (shrinkYonedaObjObjEquiv.{u + 1}.symm f)))
        erw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm]
        simp only [Equiv.apply_symm_apply]
        exact congrArg ULift.up (etaleNeighborhoodMapLift_refinement Y ξ U q.unop f) }


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual germ-to-lift map from the comapped smooth-neighborhood fiber to the native
small-base geometric fiber. The universe lift changes no scheme or marking. -/
def etaleNeighborhoodGermToLift (U : EtaleSeparatedFiniteType S) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber.obj
        ((toSmoothSite (SmoothSite.base S)).obj U) ⟶
      ULift.{u + 1} ((pointSmallEtale (ξ ≫ Y.hom)).fiber.obj ((toSmallEtale S).obj U)) :=
  colimit.desc _ (etaleNeighborhoodLiftCocone Y ξ U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The germ-to-lift map evaluates the original representative at its actual marking. -/
@[simp]
theorem etaleNeighborhoodGermToLift_fiberMk (U : EtaleSeparatedFiniteType S)
    (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    etaleNeighborhoodGermToLift Y ξ U
        (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f) =
      ULift.up (etaleNeighborhoodMapLift Y ξ U A f) := by
  have h := ConcreteCategory.congr_hom
    (colimit.ι_desc (etaleNeighborhoodLiftCocone Y ξ U) (op A))
    (shrinkYonedaObjObjEquiv.{u + 1}.symm f)
  change etaleNeighborhoodGermToLift Y ξ U
    (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f) =
      ULift.up (etaleNeighborhoodMapLift Y ξ U A
        (shrinkYonedaObjObjEquiv.{u + 1} (shrinkYonedaObjObjEquiv.{u + 1}.symm f))) at h
  simpa only [Equiv.apply_symm_apply] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual pullback and diagonal refinement prove bijectivity of the germ-to-lift map. -/
@[colib_tag "COL-1104"]
theorem etaleNeighborhoodGermToLift_bijective (U : EtaleSeparatedFiniteType S) :
    Function.Bijective (etaleNeighborhoodGermToLift Y ξ U) := by
  constructor
  · intro x y h
    obtain ⟨A, f, rfl⟩ := GrothendieckTopology.Point.ofIsCofiltered.fiberMk_jointly_surjective x
    obtain ⟨B, g, rfl⟩ := GrothendieckTopology.Point.ofIsCofiltered.fiberMk_jointly_surjective y
    rw [etaleNeighborhoodGermToLift_fiberMk, etaleNeighborhoodGermToLift_fiberMk] at h
    have hfg := congrArg ULift.down h
    obtain ⟨C, q, r, -⟩ := IsCofilteredOrEmpty.cone_objs A B
    obtain ⟨D, t, ht⟩ := exists_etaleNeighborhood_refinement_eq_of_mapLift_eq Y ξ U C
      ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map q ≫ f)
      ((SmoothSite.etaleNeighborhoodToSmooth Y ξ).map r ≫ g) (by
        simpa only [etaleNeighborhoodMapLift_refinement] using hfg)
    have heq := congrArg
      (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1}
        (p := SmoothSite.etaleNeighborhoodToSmooth Y ξ)) ht
    simp only [GrothendieckTopology.Point.ofIsCofiltered.fiberMk_map_comp] at heq
    exact heq
  · rintro ⟨z⟩
    obtain ⟨A, f, hf⟩ := exists_etaleNeighborhood_mapLift Y ξ U z
    refine ⟨GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f, ?_⟩
    rw [etaleNeighborhoodGermToLift_fiberMk, hf]

/-- The comapped smooth-neighborhood fiber and the native small-base geometric fiber
agree on every actual small-basis object. -/
def etaleNeighborhoodGermLiftIso (U : EtaleSeparatedFiniteType S) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber.obj
        ((toSmoothSite (SmoothSite.base S)).obj U) ≅
      ULift.{u + 1} ((pointSmallEtale (ξ ≫ Y.hom)).fiber.obj ((toSmallEtale S).obj U)) :=
  (Equiv.ofBijective (etaleNeighborhoodGermToLift Y ξ U)
    (etaleNeighborhoodGermToLift_bijective Y ξ U)).toIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison on geometric fibers is natural for the original small-basis scheme maps. -/
@[colib_tag "COL-1104"]
def etaleNeighborhoodBaseFiberIso :
    toSmoothSite (SmoothSite.base S) ⋙
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber ≅
      toSmallEtale S ⋙ (pointSmallEtale (ξ ≫ Y.hom)).fiber ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (etaleNeighborhoodGermLiftIso Y ξ) (by
    intro U V k
    ext x
    obtain ⟨A, f, rfl⟩ := GrothendieckTopology.Point.ofIsCofiltered.fiberMk_jointly_surjective x
    change etaleNeighborhoodGermToLift Y ξ V
        ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber.map
          ((toSmoothSite (SmoothSite.base S)).map k)
            (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f)) = _
    erw [GrothendieckTopology.Point.ofIsCofiltered.fiber_map_fiberMk,
      etaleNeighborhoodGermToLift_fiberMk]
    change ULift.up (etaleNeighborhoodMapLift Y ξ V A
      (f ≫ (toSmoothSite (SmoothSite.base S)).map k)) =
        ULift.up ((pointSmallEtale (ξ ≫ Y.hom)).fiber.map ((toSmallEtale S).map k)
          (etaleNeighborhoodGermToLift Y ξ U
            (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f)).down)
    rw [etaleNeighborhoodGermToLift_fiberMk]
    apply congrArg ULift.up
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
