/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.ContractionPermutation
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.ProjectionGeometry
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Etale.Pullback
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1PunctureBaseChange


/-! # The actual product of a chosen étale zero-section chart

The normal parameter stays last. The resulting comparison is an isomorphism
of actual neighborhood functors, not a smooth inverse-image coefficient
isomorphism. Both original projections are retained.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Contraction/ProjectionExcisionGeometry.lean`, blob
`658ae71e7f064cc3716386a67a91d0d7e1366604`.
The earlier Product base-change section remains frozen successor01. This file constructs the
actual etale chart product, whole-zero and puncture Cartesian squares, and original small-site
comparison, without Epi/HI inputs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  {E : SmoothSite (Spec R)} (b : E ⟶ affineLineCylinder.obj X)

local notation "T" => additiveGroupObject (Spec R)
local notation "Tₘ" => multiplicativeGroupObject (Spec R)

/-- The chosen chart times the homotopy line, retaining the normal coordinate last. -/
def contractionChartProduct :
    affineLineCylinder.obj E ⟶ affineLineCylinder.obj (affineLineCylinder.obj X) :=
  affineLineCylinder.map b ≫ (productSwapLastIso X T T).hom

/-- The product chart lies over its original chart, with the literal projection. -/
@[reassoc (attr := simp)]
theorem contractionChartProduct_projection :
    contractionChartProduct R X b ≫ affineLineCylinder.map ((projection T).app X) =
      (projection T).app E ≫ b := by
  change (affineLineCylinder.map b ≫ productSwapLast X T T) ≫
      affineLineCylinder.map ((projection T).app X) = _
  have hs : productSwapLast X T T ≫
      productSwapLast X T T = 𝟙 _ :=
    (productSwapLastIso X T T).hom_inv_id
  rw [Category.assoc, ← a1Projection_productSwapLast R X]
  rw [← Category.assoc (productSwapLast X T T), hs,
    Category.id_comp]
  exact (Contraction.projection T).naturality b

/-- Products preserve the full Cartesian chart square, not only the marked point. -/
theorem contractionChartProduct_isPullback :
    IsPullback (contractionChartProduct R X b).left ((projection T).app E).left
      (affineLineCylinder.map ((projection T).app X)).left b.left := by
  have h : IsPullback (affineLineCylinder.map b).left ((projection T).app E).left
      ((projection T).app (affineLineCylinder.obj X)).left b.left := by
    apply IsPullback.of_right
      (h₁₂ := (productSnd (affineLineCylinder.obj X) T).left)
      (h₂₂ := (affineLineCylinder.obj X).hom) (v₁₃ := (T).hom)
    · have hs := congrArg (fun f ↦ f.left)
        (productMap_snd b (𝟙 T))
      change (affineLineCylinder.map b).left ≫ (productSnd (affineLineCylinder.obj X) T).left =
        (productSnd E T).left ≫ 𝟙 _ at hs
      rw [hs, Category.comp_id, MorphismProperty.Over.w b]
      exact (IsPullback.of_hasPullback E.hom (T).hom).flip
    · exact congrArg (fun f ↦ f.left) (((Contraction.projection T).naturality b))
    · exact (IsPullback.of_hasPullback (affineLineCylinder.obj X).hom (T).hom).flip
  refine h.of_iso (Iso.refl _)
    ((forgetScheme (Spec R)).mapIso
      (productSwapLastIso X T T))
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change ((projection T).app (affineLineCylinder.obj X)).left =
      (productSwapLast X T T).left ≫
        (affineLineCylinder.map ((projection T).app X)).left
    have hs : productSwapLast X T T ≫ productSwapLast X T T = 𝟙 _ :=
      (productSwapLastIso X T T).hom_inv_id
    have hπ : (projection T).app (affineLineCylinder.obj X) =
        productSwapLast X T T ≫ affineLineCylinder.map ((projection T).app X) := by
      rw [← a1Projection_productSwapLast R X, ← Category.assoc, hs, Category.id_comp]
    exact congrArg (fun f ↦ f.left) hπ
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

instance contractionChartProduct_etale [Etale b.left] :
    Etale (contractionChartProduct R X b).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale) (contractionChartProduct_isPullback R X b).flip inferInstance

/-- The whole zero section is retained after taking the chart product. -/
theorem contractionChartProduct_zero {a : X ⟶ E}
    (ha : a ≫ b = nativeAffineSection R X 0) :
    affineLineCylinder.map a ≫ contractionChartProduct R X b =
      nativeAffineSection R (affineLineCylinder.obj X) 0 := by
  rw [contractionChartProduct, ← Category.assoc, ← Functor.map_comp, ha,
    ← a1Section_productSwapLast R X 0]
  have hs : productSwapLast X T T ≫
      productSwapLast X T T = 𝟙 _ :=
    (productSwapLastIso X T T).hom_inv_id
  change (_ ≫ productSwapLast X T T) ≫
      productSwapLast X T T = _
  rw [Category.assoc, hs, Category.comp_id]

/-- The punctured product chart uses the same displayed parameter permutation. -/
def contractionChartPunctureProduct {U : SmoothSite (Spec R)}
    (q : U ⟶ torusCylinder.obj X) :
    affineLineCylinder.obj U ⟶ torusCylinder.obj (affineLineCylinder.obj X) :=
  affineLineCylinder.map q ≫ (productSwapLastIso X Tₘ T).hom

/-- The original open immersion is retained by the actual parameter permutation. -/
theorem contractionChartProduct_open :
    affineLineCylinder.map (openInclusion.app X) ≫
        (productSwapLastIso X T T).hom =
      (productSwapLastIso X Tₘ T).hom ≫
        openInclusion.app (affineLineCylinder.obj X) := by
  let g := multiplicativeGroupOpen (Spec R)
  change productMap (productMap (𝟙 X) g) (𝟙 T) ≫ productSwapLast X T T =
    productSwapLast X Tₘ T ≫ productMap (𝟙 (product X T)) g
  simpa only [productMap_id] using productSwapLast_naturality X Tₘ T (𝟙 X) g (𝟙 T)

/-- A chosen punctured chart square remains Cartesian after product with the
whole homotopy line, with the normal coordinate still last. -/
theorem contractionChartPunctureProduct_isPullback
    {U : SmoothSite (Spec R)} (j : U ⟶ E) (q : U ⟶ torusCylinder.obj X)
    (hpb : IsPullback q j (openInclusion.app X) b) :
    IsPullback (contractionChartPunctureProduct R X q) (affineLineCylinder.map j)
      (openInclusion.app (affineLineCylinder.obj X)) (contractionChartProduct R X b) := by
  have h := (parameterProduct T).map_isPullback hpb
  refine h.of_iso (Iso.refl _)
    (productSwapLastIso X Tₘ T)
    (Iso.refl _) (productSwapLastIso X T T) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact contractionChartProduct_open R X
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType



variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {E : SmoothSite (Spec (.of k))} (b : E ⟶ affineLineCylinder.obj X)
  [Etale b.left]

local notation "b₁" => SmoothSite.contractionChartProduct (CommRingCat.of k) X b
local notation "T" => SmoothSite.additiveGroupObject (Spec (CommRingCat.of k))
local notation "p" => affineLineCylinder.map (NatTrans.app (projection T) X)
local notation "πE" => NatTrans.app (projection T) E

omit [Etale b.left] in
/-- The product chart gives the original Cartesian square in the smooth category. -/
theorem contractionChartProduct_isPullback : IsPullback b₁ πE p b :=
  IsPullback.of_map_of_faithful (SmoothSite.forgetScheme (Spec (.of k)))
    (SmoothSite.contractionChartProduct_isPullback (CommRingCat.of k) X b)

/-- Étale chart restriction and product pullback commute on the actual small sites. -/
def contractionChartProjectionBaseChangeIso :
    baseChange (πE).left ⋙ etalePostcompose (b₁).left ≅
      etalePostcompose b.left ⋙ baseChange (p).left :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk
    (puncturedNeighborhoodIso p b πE b₁
      (contractionChartProduct_isPullback X b) V)
    (puncturedNeighborhoodIso_hom_snd p b πE b₁
      (contractionChartProduct_isPullback X b) V)) (by
        intro V W f
        have hsf : ((baseChange (πE).left).map f).left ≫
            pullback.fst W.hom (πE).left =
          pullback.fst V.hom (πE).left ≫ f.left := pullback.lift_fst _ _ _
        have hss : ((baseChange (πE).left).map f).left ≫
            pullback.snd W.hom (πE).left =
          pullback.snd V.hom (πE).left := pullback.lift_snd _ _ _
        have htf : ((baseChange (p).left).map ((etalePostcompose b.left).map f)).left ≫
            pullback.fst (W.hom ≫ b.left) (p).left =
          pullback.fst (V.hom ≫ b.left) (p).left ≫ f.left := pullback.lift_fst _ _ _
        have hts : ((baseChange (p).left).map ((etalePostcompose b.left).map f)).left ≫
            pullback.snd (W.hom ≫ b.left) (p).left =
          pullback.snd (V.hom ≫ b.left) (p).left := pullback.lift_snd _ _ _
        apply MorphismProperty.Over.Hom.ext
        change ((baseChange (πE).left).map f).left ≫
            (puncturedNeighborhoodIso p b πE b₁
              (contractionChartProduct_isPullback X b) W).hom =
          (puncturedNeighborhoodIso p b πE b₁
            (contractionChartProduct_isPullback X b) V).hom ≫
            ((baseChange (p).left).map ((etalePostcompose b.left).map f)).left
        apply pullback.hom_ext
        · rw [Category.assoc, puncturedNeighborhoodIso_hom_fst, Category.assoc,
            htf, ← Category.assoc, puncturedNeighborhoodIso_hom_fst, hsf]
        · rw [Category.assoc, puncturedNeighborhoodIso_hom_snd, Category.assoc,
            hts, puncturedNeighborhoodIso_hom_snd, ← Category.assoc, hss])

/-- The comparison leaves unchanged the original base-neighborhood projection. -/
@[reassoc (attr := simp)]
theorem contractionChartProjectionBaseChangeIso_fst (V : EtaleSeparatedFiniteType E.left) :
    ((contractionChartProjectionBaseChangeIso X b).hom.app V).left ≫
        pullback.fst (V.hom ≫ b.left) (p).left = pullback.fst V.hom (πE).left :=
  puncturedNeighborhoodIso_hom_fst p b πE b₁
    (contractionChartProduct_isPullback X b) V

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
