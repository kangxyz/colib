/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ParameterProduct
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-! # The literal cylinder neighborhoods used by the contraction boundary map -/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Contraction/Geometry.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `99dcb19f77dab7db49daa83a3b4782640caf60e8`.
The actual native additive and multiplicative parameter objects and the existing
small-site image adjunction are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- Native constant sections commute with the actual cylinder maps. -/
@[reassoc]
theorem nativeAffineSection_naturality (R : CommRingCat.{u})
    {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) (a : R) :
    nativeAffineSection R X a ≫ affineLineCylinder.map f =
      f ≫ nativeAffineSection R Y a := by
  apply product_hom_ext <;>
    simp [nativeAffineSection, affineLineCylinder, parameterProduct, Category.assoc]

/-- The genuine Laurent open is monic in the smooth category. -/
instance openInclusion_mono {S : Scheme.{u}} (X : SmoothSite S) :
    Mono (openInclusion.app X) := by
  exact (SmoothSite.forgetScheme S).mono_of_mono_map (by
    change Mono (openInclusion.app X).left
    infer_instance)

end AlgebraicGeometry.Scheme.SmoothSite.Contraction

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- The literal étale affine-line cylinder over a base neighborhood. -/
abbrev cylinderNeighborhood := parameterProduct X (SmoothSite.additiveGroupObject (Spec (.of k)))

/-- The actual pullback of this cylinder to the punctured ambient cylinder. -/
abbrev puncturedNeighborhood :=
  cylinderNeighborhood X ⋙ baseChange (SmoothSite.Contraction.openInclusion.app X).left

/-- The actual pullback of the cylinder to the ambient zero section. -/
abbrev zeroNeighborhood :=
  cylinderNeighborhood X ⋙ baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left

/-- The punctured neighborhood maps to the original literal Laurent product. -/
def puncturedProjection (V : EtaleSeparatedFiniteType X.left) :
    (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj ((puncturedNeighborhood X).obj V) ⟶
      SmoothSite.Contraction.torusCylinder.obj ((toSmoothSite X).obj V) :=
  SmoothSite.productLift
    ((restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app
        ((cylinderNeighborhood X).obj V) ≫
      (parameterProductUnderlyingIso X (SmoothSite.additiveGroupObject (Spec (.of k)))).hom.app V ≫
      SmoothSite.productFst _ _)
    (toBase (SmoothSite.Contraction.torusCylinder.obj X) ((puncturedNeighborhood X).obj V) ≫
      SmoothSite.productSnd X (SmoothSite.multiplicativeGroupObject (Spec (.of k))))

/-- The original affine-line restriction agrees with the actual open pullback projection. -/
theorem puncturedProjection_open (V : EtaleSeparatedFiniteType X.left) :
    puncturedProjection X V ≫
      SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj V) =
      (restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app
        ((cylinderNeighborhood X).obj V) ≫
      (parameterProductUnderlyingIso X (SmoothSite.additiveGroupObject (Spec (.of k)))).hom.app V := by
  apply SmoothSite.product_hom_ext
  · simp [puncturedProjection, SmoothSite.Contraction.openInclusion, SmoothSite.Contraction.parameterMap]
  · simp only [puncturedProjection, SmoothSite.Contraction.openInclusion, SmoothSite.Contraction.parameterMap, Category.assoc,
      SmoothSite.productMap_snd, SmoothSite.productLift_snd_assoc]
    apply MorphismProperty.Over.Hom.ext
    change (pullback.snd ((cylinderNeighborhood X).obj V).hom
        (SmoothSite.Contraction.openInclusion.app X).left ≫
        (SmoothSite.productSnd X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).left) ≫
        (SmoothSite.multiplicativeGroupOpen (Spec (.of k))).left =
      pullback.fst ((cylinderNeighborhood X).obj V).hom
        (SmoothSite.Contraction.openInclusion.app X).left ≫ 𝟙 _ ≫
        (SmoothSite.productSnd ((toSmoothSite X).obj V) (SmoothSite.additiveGroupObject (Spec (.of k)))).left
    rw [Category.id_comp]
    have h := pullback.condition
      (f := ((cylinderNeighborhood X).obj V).hom)
      (g := (SmoothSite.Contraction.openInclusion.app X).left)
    have h' := congrArg (fun a ↦ a ≫ (SmoothSite.productSnd X
      (SmoothSite.additiveGroupObject (Spec (.of k)))).left) h
    have ho := congrArg (fun a ↦ a.left)
      (SmoothSite.productMap_snd (𝟙 X) (SmoothSite.multiplicativeGroupOpen (Spec (.of k))))
    have hc := congrArg (fun a ↦ a.left)
      (SmoothSite.productMap_snd (toBase X V) (𝟙 (SmoothSite.additiveGroupObject (Spec (.of k)))))
    change (SmoothSite.Contraction.openInclusion.app X).left ≫
      (SmoothSite.productSnd X (SmoothSite.additiveGroupObject (Spec (.of k)))).left = _ at ho
    change ((cylinderNeighborhood X).obj V).hom ≫
      (SmoothSite.productSnd X (SmoothSite.additiveGroupObject (Spec (.of k)))).left =
      (SmoothSite.productSnd ((toSmoothSite X).obj V)
        (SmoothSite.additiveGroupObject (Spec (.of k)))).left ≫ 𝟙 _ at hc
    simp only [Category.assoc, ho, hc, Category.comp_id] at h'
    exact h'.symm

/-- The actual affine comparison is natural in the étale base neighborhood. -/
def affineProjection :
    puncturedNeighborhood X ⋙ toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X) ⟶
      toSmoothSite X ⋙ SmoothSite.Contraction.parameterProduct (SmoothSite.additiveGroupObject (Spec (.of k))) :=
  Functor.whiskerLeft (cylinderNeighborhood X)
    (restrictionProjection (SmoothSite.Contraction.openInclusion.app X)) ≫
    (parameterProductUnderlyingIso X (SmoothSite.additiveGroupObject (Spec (.of k)))).hom

/-- Naturality of the original Laurent restriction on the neighborhood products. -/
theorem puncturedProjection_naturality {V W : EtaleSeparatedFiniteType X.left} (f : V ⟶ W) :
    (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).map
        ((puncturedNeighborhood X).map f) ≫ puncturedProjection X W =
      puncturedProjection X V ≫
        SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) := by
  apply (cancel_mono (SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj W))).mp
  have hn : SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj V) ≫
      SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 (SmoothSite.additiveGroupObject (Spec (.of k)))) =
      SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) ≫
        SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj W) := by
    simp only [SmoothSite.Contraction.openInclusion, SmoothSite.Contraction.parameterMap, ← SmoothSite.productMap_comp,
      Category.comp_id, Category.id_comp]
  rw [Category.assoc, puncturedProjection_open, Category.assoc, ← hn,
    ← Category.assoc (puncturedProjection X V), puncturedProjection_open]
  exact (affineProjection X).naturality f

/-- The original zero section lifts a base neighborhood into the true closed pullback. -/
def zeroNeighborhoodLift (V : EtaleSeparatedFiniteType X.left) :
    V ⟶ (zeroNeighborhood X).obj V :=
  MorphismProperty.Over.homMk
    (pullback.lift (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left
      V.hom (by
        exact congrArg (fun a ↦ a.left)
          (SmoothSite.Contraction.nativeAffineSection_naturality (.of k) (toBase X V) 0)))
    (pullback.lift_snd _ _ _)

/-- The lifted zero sections form a natural map of actual small-site functors. -/
def zeroNeighborhoodLiftNat : 𝟭 (EtaleSeparatedFiniteType X.left) ⟶ zeroNeighborhood X where
  app := zeroNeighborhoodLift X
  naturality V W f := by
    have hf (V : EtaleSeparatedFiniteType X.left) :
        (zeroNeighborhoodLift X V).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom
            (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left =
          (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left :=
      pullback.lift_fst _ _ _
    have hs (V : EtaleSeparatedFiniteType X.left) :
        (zeroNeighborhoodLift X V).left ≫
          pullback.snd ((cylinderNeighborhood X).obj V).hom
            (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left = V.hom :=
      pullback.lift_snd _ _ _
    have hmf : ((zeroNeighborhood X).map f).left ≫
        pullback.fst ((cylinderNeighborhood X).obj W).hom
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left =
        pullback.fst ((cylinderNeighborhood X).obj V).hom
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left ≫
          (SmoothSite.productMap ((toSmoothSite X).map f)
            (𝟙 (SmoothSite.additiveGroupObject (Spec (.of k))))).left :=
      pullback.lift_fst _ _ _
    have hms : ((zeroNeighborhood X).map f).left ≫
        pullback.snd ((cylinderNeighborhood X).obj W).hom
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left =
        pullback.snd ((cylinderNeighborhood X).obj V).hom
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left :=
      pullback.lift_snd _ _ _
    apply MorphismProperty.Over.Hom.ext
    change f.left ≫ (zeroNeighborhoodLift X W).left =
      (zeroNeighborhoodLift X V).left ≫ ((zeroNeighborhood X).map f).left
    apply pullback.hom_ext
    · rw [Category.assoc, hf, Category.assoc, hmf, ← Category.assoc, hf]
      exact (congrArg (fun a ↦ a.left)
        (SmoothSite.Contraction.nativeAffineSection_naturality (.of k) ((toSmoothSite X).map f) 0)).symm
    · rw [Category.assoc, hs, Category.assoc, hms, hs, MorphismProperty.Over.w]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary

