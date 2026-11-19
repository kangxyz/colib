/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.PointSupport

/-! # Restriction of point supports along open immersions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable {Y X : Sm(k)} (f : Y ⟶ X) [IsOpenImmersion f.left]

/-- Under an open immersion, the inverse image of the closure of an image point
is the closure of the original point. -/
theorem preimage_pointClosure_eq (y : Y.left) :
    f.left ⁻¹' closure ({f.left y} : Set X.left) = closure ({y} : Set Y.left) := by
  simpa only [Set.image_singleton] using
    (f.left.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image {y}).symm

/-- Image of the pointed open neighbourhood under the given open immersion. -/
abbrev pointSupportImageNeighborhoods (y : Y.left) :
    PointSupportNeighborhoods k Y y ⥤ PointSupportNeighborhoods k X (f.left y) :=
  Topology.IsOpenEmbedding.functorNhds (f := f.left.base) f.left.isOpenEmbedding y

/-- Every neighbourhood of an image point can be shrunk inside the open image. -/
instance (y : Y.left) : (pointSupportImageNeighborhoods k f y).op.Final :=
  Functor.final_of_adjunction
    (Topology.IsOpenEmbedding.adjunctionNhds (f := f.left.base) f.left.isOpenEmbedding y).op

/-- Taking images of pointed opens carries their original complements to one another. -/
theorem image_pointSupportComplement (y : Y.left) (V : Y.left.Opens) :
    f.left ''ᵁ (pointSupportComplement k Y y V) =
      pointSupportComplement k X (f.left y) (f.left ''ᵁ V) := by
  ext z
  change (z ∈ f.left '' ((V : Set Y.left) ∩ (closure {y})ᶜ)) ↔
    (z ∈ f.left '' (V : Set Y.left) ∧ z ∉ closure {f.left y})
  constructor
  · rintro ⟨a, ⟨haV, haC⟩, rfl⟩
    refine ⟨⟨a, haV, rfl⟩, ?_⟩
    change a ∉ f.left ⁻¹' closure {f.left y}
    rw [preimage_pointClosure_eq]
    exact haC
  · rintro ⟨⟨a, haV, rfl⟩, haC⟩
    refine ⟨a, ⟨haV, ?_⟩, rfl⟩
    change a ∉ f.left ⁻¹' closure {f.left y} at haC
    rwa [preimage_pointClosure_eq] at haC

private theorem range_openImage (V : Y.left.Opens) (W : X.left.Opens)
    (h : f.left ''ᵁ V = W) : Set.range (V.ι ≫ f.left) = Set.range W.ι := by
  rw [show (⇑(V.ι ≫ f.left)) = f.left ∘ V.ι from rfl, Set.range_comp,
    Scheme.Opens.range_ι, Scheme.Opens.range_ι, ← h]
  rfl

private def openImageIso (V : Y.left.Opens) (W : X.left.Opens)
    (h : f.left ''ᵁ V = W) : (SmoothSite.opensFunctor Y).obj V ≅
      (SmoothSite.opensFunctor X).obj W := by
  let j := SmoothSite.openInclusion Y V ≫ f
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ f.left))
  have hr : Set.range j.left = Set.range W.ι := range_openImage k f V W h
  let e := IsOpenImmersion.isoOfRangeEq j.left W.ι hr
  exact MorphismProperty.Over.isoMk e (by
    change e.hom ≫ W.ι ≫ X.hom = _
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, MorphismProperty.Over.w j])

@[reassoc]
private theorem openImageIso_hom_comp (V : Y.left.Opens) (W : X.left.Opens)
    (h : f.left ''ᵁ V = W) :
    (openImageIso k f V W h).hom ≫ SmoothSite.openInclusion X W =
      SmoothSite.openInclusion Y V ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  let : IsOpenImmersion (SmoothSite.openInclusion Y V ≫ f).left := inferInstanceAs
    (IsOpenImmersion (V.ι ≫ f.left))
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (range_openImage k f V W h)

private instance openInclusion_mono {T : Sm(k)} (U : T.left.Opens) :
    Mono (SmoothSite.openInclusion T U) :=
  (SmoothSite.forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono U.ι))

@[reassoc]
private theorem relativeOpenInclusion_comp_inclusion {T : Sm(k)} {U V : T.left.Opens}
    (h : U ≤ V) :
    (SmoothSite.opensFunctor T).map (homOfLE h) ≫ SmoothSite.openInclusion T V =
      SmoothSite.openInclusion T U := MorphismProperty.Over.Hom.ext (T.left.homOfLE_ι h)

/-- The pairs on an open subscheme are the original pairs on their images. -/
@[no_expose]
def pointSupportImagePairIso (y : Y.left) (U : PointSupportNeighborhoods k Y y) :
    pointSupportPair k Y y U ≅
      pointSupportPair k X (f.left y) ((pointSupportImageNeighborhoods k f y).obj U) := by
  let V := (pointSupportImageNeighborhoods k f y).obj U
  let l := openImageIso k f (pointSupportComplement k Y y U.1)
    (pointSupportComplement k X (f.left y) V.1) (image_pointSupportComplement k f y U.1)
  let r := openImageIso k f U.1 V.1 rfl
  refine Arrow.isoMk l r ?_
  apply (cancel_mono (SmoothSite.openInclusion X V.1)).mp
  change (l.hom ≫ (SmoothSite.opensFunctor X).map (homOfLE inf_le_left)) ≫ _ =
    ((SmoothSite.opensFunctor Y).map (homOfLE inf_le_left) ≫ r.hom) ≫ _
  simp only [Category.assoc, relativeOpenInclusion_comp_inclusion, l, r, openImageIso_hom_comp,
    relativeOpenInclusion_comp_inclusion_assoc]
  rfl

/-- The ambient component of the pair identification is the original restriction. -/
@[reassoc]
theorem pointSupportImagePairIso_hom_right_comp (y : Y.left)
    (U : PointSupportNeighborhoods k Y y) :
    (pointSupportImagePairIso k f y U).hom.right ≫
        SmoothSite.openInclusion X ((pointSupportImageNeighborhoods k f y).obj U).1 =
      SmoothSite.openInclusion Y U.1 ≫ f := openImageIso_hom_comp k f U.1 _ rfl

private def pointSupportImagePairDiagramIso (y : Y.left) :
    pointSupportPairFunctor k Y y ≅
      pointSupportImageNeighborhoods k f y ⋙ pointSupportPairFunctor k X (f.left y) :=
  NatIso.ofComponents (pointSupportImagePairIso k f y) (by
    intro U V a
    apply Arrow.hom_ext
    · let W := pointSupportComplement k X (f.left y)
        ((pointSupportImageNeighborhoods k f y).obj V).1
      let W' := pointSupportComplement k X (f.left y)
        ((pointSupportImageNeighborhoods k f y).obj U).1
      let eU := openImageIso k f (pointSupportComplement k Y y U.1) W'
        (image_pointSupportComplement k f y U.1)
      let eV := openImageIso k f (pointSupportComplement k Y y V.1) W
        (image_pointSupportComplement k f y V.1)
      let b := (pointSupportImageNeighborhoods k f y).map a
      let hY : pointSupportComplement k Y y U.1 ≤ pointSupportComplement k Y y V.1 :=
        inf_le_inf_right (Closeds.closure {y}).compl a.le
      let hX : W' ≤ W := inf_le_inf_right (Closeds.closure {f.left y}).compl b.le
      apply (cancel_mono (SmoothSite.openInclusion X W)).mp
      change ((SmoothSite.opensFunctor Y).map (homOfLE hY) ≫ eV.hom) ≫ _ =
        (eU.hom ≫ (SmoothSite.opensFunctor X).map (homOfLE hX)) ≫ _
      have eV₁ : eV.hom ≫ SmoothSite.openInclusion X W =
          SmoothSite.openInclusion Y (pointSupportComplement k Y y V.1) ≫ f :=
        openImageIso_hom_comp k f _ _ _
      have eU₁ : eU.hom ≫ SmoothSite.openInclusion X W' =
          SmoothSite.openInclusion Y (pointSupportComplement k Y y U.1) ≫ f :=
        openImageIso_hom_comp k f _ _ _
      simp only [Category.assoc, eV₁, relativeOpenInclusion_comp_inclusion_assoc k hY,
        relativeOpenInclusion_comp_inclusion k hX, eU₁]
    · apply (cancel_mono (SmoothSite.openInclusion X
          ((pointSupportImageNeighborhoods k f y).obj V).1)).mp
      change ((SmoothSite.opensFunctor Y).map (homOfLE a.le) ≫
        (pointSupportImagePairIso k f y V).hom.right) ≫ _ =
        ((pointSupportImagePairIso k f y U).hom.right ≫
          (SmoothSite.opensFunctor X).map
            (homOfLE ((pointSupportImageNeighborhoods k f y).map a).le)) ≫ _
      simp only [Category.assoc, pointSupportImagePairIso_hom_right_comp,
        relativeOpenInclusion_comp_inclusion, relativeOpenInclusion_comp_inclusion_assoc])

private theorem map_op_comp_eq {A B : Type*} [Category* A] [Category* B] (F : Aᵒᵖ ⥤ B)
    {J K L M : A} {a : J ⟶ K} {b : K ⟶ M} {c : J ⟶ L} {d : L ⟶ M}
    (e : a ≫ b = c ≫ d) : F.map b.op ≫ F.map a.op = F.map d.op ≫ F.map c.op :=
  (F.map_comp b.op a.op).symm.trans
    ((F.congr_map (congrArg Quiver.Hom.op e)).trans (F.map_comp d.op c.op))

private def colimitImageIso {I J C : Type*}
    [Category* I] [Category* J] [Category* C] [HasColimitsOfShape I C]
    (L : I ⥤ J) [L.Final] (D : J ⥤ C) [HasColimit D] (G : I ⥤ C)
    (e : L ⋙ D ≅ G) : colimit D ≅ colimit G :=
  (Functor.Final.colimitIso L D).symm ≪≫ colim.mapIso e

private theorem colimitImageIso_generator {I J C : Type*}
    [Category* I] [Category* J] [Category* C] [HasColimitsOfShape I C]
    (L : I ⥤ J) [L.Final] (D : J ⥤ C) [HasColimit D] (G : I ⥤ C)
    (e : L ⋙ D ≅ G) (U : I) :
    colimit.ι D (L.obj U) ≫ (colimitImageIso L D G e).hom =
      e.hom.app U ≫ colimit.ι G U := by
  change colimit.ι D (L.obj U) ≫ (Functor.Final.colimitIso L D).inv ≫ colimMap e.hom = _
  rw [Functor.Final.ι_colimitIso_inv_assoc, ι_colimMap]

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

/-- The isomorphism of the original point supports on an image neighbourhood. -/
def pointSupportImageRestrictionIsoAt (K : DM(k)) (n : ℤ) (y : Y.left)
    (U : PointSupportNeighborhoods k Y y) :
    (pointSupportCohomologyDiagram k X K n (f.left y)).obj
      (op ((pointSupportImageNeighborhoods k f y).obj U)) ≅
      (pointSupportCohomologyDiagram k Y K n y).obj (op U) :=
  let H := effectivePairCohomology k K n
  let e := pointSupportImagePairIso k f y U
  H.mapIso e.op

/-- The cohomology map of the original pair on an image neighbourhood. -/
abbrev pointSupportImageRestrictionMap (K : DM(k)) (n : ℤ) (y : Y.left)
    (U : PointSupportNeighborhoods k Y y) :=
  (pointSupportImageRestrictionIsoAt k f K n y U).hom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def pointSupportImageRestrictionDiagramIso (K : DM(k)) (n : ℤ) (y : Y.left) :
    (pointSupportImageNeighborhoods k f y).op ⋙
        pointSupportCohomologyDiagram k X K n (f.left y) ≅
      pointSupportCohomologyDiagram k Y K n y := by
  refine NatIso.ofComponents (fun U ↦ pointSupportImageRestrictionIsoAt k f K n y U.unop) ?_
  intro U V g
  let L := pointSupportImageNeighborhoods k f y
  let D := L.op ⋙ pointSupportCohomologyDiagram k X K n (f.left y)
  let G := pointSupportCohomologyDiagram k Y K n y
  let H := effectivePairCohomology k K n
  let P := pointSupportPairFunctor k X (f.left y)
  let Q := pointSupportPairFunctor k Y y
  let e := pointSupportImagePairDiagramIso k f y
  let p := P.map (L.map g.unop)
  let q := Q.map g.unop
  let eU := (pointSupportImagePairIso k f y U.unop).hom
  let eV := (pointSupportImagePairIso k f y V.unop).hom
  have h : eV ≫ p = q ≫ eU := (e.hom.naturality g.unop).symm
  let a : D.obj U ⟶ D.obj V := H.map p.op
  let b : D.obj V ⟶ G.obj V := H.map eV.op
  let c : D.obj U ⟶ G.obj U := H.map eU.op
  let d : G.obj U ⟶ G.obj V := H.map q.op
  have ha : D.map g = a := rfl
  have hb : pointSupportImageRestrictionMap k f K n y V.unop = b := rfl
  have hc : pointSupportImageRestrictionMap k f K n y U.unop = c := rfl
  have hd : G.map g = d := rfl
  have hab : a ≫ b = c ≫ d := map_op_comp_eq H h
  exact (congrArg₂ (· ≫ ·) ha hb).trans (hab.trans (congrArg₂ (· ≫ ·) hc hd).symm)

variable [UnivLE.{u, w'}]

/-- Restriction along the original open immersion is an isomorphism on the surviving point group. -/
@[no_expose]
def pointSupportOpenRestrictionIso (K : DM(k)) (n : ℤ) (y : Y.left) :
    pointSupportCohomology k X K n (f.left y) ≅ pointSupportCohomology k Y K n y :=
  colimitImageIso (pointSupportImageNeighborhoods k f y).op
    (pointSupportCohomologyDiagram k X K n (f.left y)) (pointSupportCohomologyDiagram k Y K n y)
    (pointSupportImageRestrictionDiagramIso k f K n y)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The point restriction is induced by the map of the original relative pairs. -/
@[reassoc]
theorem pointSupportι_openRestrictionIso (K : DM(k)) (n : ℤ) (y : Y.left)
    (U : PointSupportNeighborhoods k Y y) :
    pointSupportι k X K n (f.left y) ((pointSupportImageNeighborhoods k f y).obj U) ≫
      (pointSupportOpenRestrictionIso k f K n y).hom =
      pointSupportImageRestrictionMap k f K n y U ≫ pointSupportι k Y K n y U := by
  let L := (pointSupportImageNeighborhoods k f y).op
  let D := pointSupportCohomologyDiagram k X K n (f.left y)
  let G := pointSupportCohomologyDiagram k Y K n y
  exact colimitImageIso_generator L D G (pointSupportImageRestrictionDiagramIso k f K n y) (op U)

end AlgebraicGeometry.MotivicHomotopy
