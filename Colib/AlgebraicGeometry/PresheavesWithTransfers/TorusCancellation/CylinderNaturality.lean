/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatSingleFiber
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI

/-!
# Naturality of the parameter projection and affine sections on correspondences

On an admissible prime, dropping the exterior parameter compares the same
whole support with the Cartesian fiber of the original prime. The actual
finite maps agree under the two support isomorphisms. Signed extension then
gives naturality of the projection and the constant affine sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)

section Projection

variable (X Y T : SmoothSite (Spec (CommRingCat.of k))) [GeometricallyIntegral T.hom]

local notation "Xₜ" => SmoothSite.product X T
local notation "Yₜ" => SmoothSite.product Y T

private theorem parameterProduct_projection_single
    (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    (parameterProduct T).map (singleFiniteCorrespondence X.hom Y.hom z hz 1) ≫
        γ (SmoothSite.productFst Y T) =
      γ (SmoothSite.productFst X T) ≫ singleFiniteCorrespondence X.hom Y.hom z hz 1 := by
  classical
  let p := SmoothSite.productFst X T
  let q := SmoothSite.productFst Y T
  let W := integralComponentAt z
  let zₜ := nativeExteriorPoint X Y T z hz
  let hzₜ := nativeExteriorPoint_admissible X Y T z hz
  let Wₜ := integralComponentAt zₜ
  let : Flat p.left := inferInstanceAs (Flat (pullback.fst X.hom T.hom))
  let : IsFinite (Wₜ.subschemeι ≫ pullback.fst (Xₜ).hom (Yₜ).hom) := hzₜ.1
  let : IsNoetherian ((𝟭 Scheme).obj (Xₜ).left) :=
    inferInstanceAs (IsNoetherian (Xₜ).left)
  let : IsNoetherian Wₜ.subscheme :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian
        (Wₜ.subschemeι ≫ pullback.fst (Xₜ).hom (Yₜ).hom)
  let : IsIntegral Wₜ.subscheme := isIntegral_integralComponentAt zₜ
  let r := correspondenceGraphPostcompositionMap (Xₜ).hom (Yₜ).hom Y.hom
    q.left (MorphismProperty.Over.w q) zₜ
  let l := correspondenceGraphFiberMap (Xₜ).hom X.hom Y.hom
    z p.left (MorphismProperty.Over.w p)
  let : IsFinite r := isFinite_correspondenceGraphPostcompositionMap _ _ _ _ _ _ hzₜ
  let : IsFinite l := isFinite_correspondenceGraphFiberMap _ _ _ _ _ _ hz
  let : IsNoetherian (correspondenceGraphFiber X.hom Y.hom z p.left) :=
    isNoetherian_correspondenceGraphFiber X.hom Y.hom z p.left hz
  let H := exteriorIdentitySource_isPullback X Y T W
  let e := nativeExteriorSupportIso X Y T z hz
  let d := H.isoPullback
  let : IsNoetherian (exteriorIdentitySupport X Y T W) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian e.hom
  let : IsNoetherian
      (pullback (pullback.fst X.hom T.hom) (exteriorSupportSourceProjection X Y W)) :=
    inferInstanceAs (IsNoetherian (correspondenceGraphFiber X.hom Y.hom z p.left))
  have he : e.hom ≫ r = d.hom ≫ l := by
    apply pullback.hom_ext
    · simp only [Category.assoc, r, l, correspondenceGraphPostcompositionMap_fst,
        correspondenceGraphFiberMap_fst]
      exact (nativeExteriorSupportIso_hom_source X Y T z hz).trans H.isoPullback_hom_fst.symm
    · simp only [Category.assoc, r, l, correspondenceGraphPostcompositionMap_snd,
        correspondenceGraphFiberMap_snd]
      calc
        _ = exteriorIdentityTarget X Y T W ≫ q.left :=
          nativeExteriorSupportIso_hom_target_assoc X Y T z hz q.left
        _ = pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫
            exteriorSupportTargetProjection X Y W :=
          exteriorIdentityTarget_fst X Y T W
        _ = _ := (H.isoPullback_hom_snd_assoc (exteriorSupportTargetProjection X Y W)).symm
  change nativeExterior X Y T (singleFiniteCorrespondence X.hom Y.hom z hz 1) ≫ γ q = _
  rw [nativeExterior_single, one_zsmul]
  apply Subtype.ext
  calc
    _ = finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle Wₜ.subscheme) := by
      rw [AlgebraicCycle.fundamentalCycle_eq_single_genericPoint]
      exact nativeExteriorPrime_graph_right_val X Y T z hz Y q
    _ = finiteCyclePushforward (e.hom ≫ r)
        (AlgebraicCycle.fundamentalCycle (exteriorIdentitySupport X Y T W)) := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso e]
    _ = finiteCyclePushforward (d.hom ≫ l)
        (AlgebraicCycle.fundamentalCycle (exteriorIdentitySupport X Y T W)) :=
      finiteCyclePushforward_congr _ _ he _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso d]
      exact (graph_comp_single_val_eq_fiber_of_flat p z hz).symm

/-- The graph of the parameter projection commutes with the exterior identity on signed cycles. -/
@[reassoc]
theorem parameterProduct_projection_naturality (α : Cor.mk X ⟶ Cor.mk Y) :
    (parameterProduct T).map α ≫ γ (SmoothSite.productFst Y T) =
      γ (SmoothSite.productFst X T) ≫ α := by
  let F := parameterProduct T
  have h : (Preadditive.rightComp (F.obj (Cor.mk X)) (γ (SmoothSite.productFst Y T))).comp
      F.mapAddHom = Preadditive.leftComp (Cor.mk Y) (γ (SmoothSite.productFst X T)) := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    exact parameterProduct_projection_single X Y T z hz
  exact DFunLike.congr_fun h α

end Projection

/-- The literal affine section is natural for arbitrary signed finite correspondences. -/
@[reassoc]
theorem nativeAffineSection_graph_naturality
    {X Y : SmoothSite (Spec (CommRingCat.of k))} (α : Cor.mk X ⟶ Cor.mk Y) (a : k) :
    γ (nativeAffineSection (.of k) X a) ≫
        (parameterProduct (additiveGroupObject (Spec (.of k)))).map α =
      α ≫ γ (nativeAffineSection (.of k) Y a) := by
  let B := SmoothSite.base (Spec (.of k))
  let A := additiveGroupObject (Spec (.of k))
  let : GeometricallyIntegral B.hom := PresheafWithTransfers.base_geometricallyIntegral (k := k)
  let : GeometricallyIntegral A.hom :=
    inferInstanceAs (GeometricallyIntegral (additiveGroupObject (Spec (.of k))).hom)
  let c : B ⟶ A := polynomialAffinePoint (.of k) a ≫ (affineLinePolynomialIso (.of k)).inv
  let eX := (graphFunctor k).mapIso (productBaseIso X)
  let eY := (graphFunctor k).mapIso (productBaseIso Y)
  have hp : (parameterProduct B).map α ≫ eY.hom = eX.hom ≫ α :=
    parameterProduct_projection_naturality X Y B α
  have hi : eX.inv ≫ (parameterProduct B).map α = α ≫ eY.inv := by
    calc
      _ = eX.inv ≫ ((parameterProduct B).map α ≫ eY.hom) ≫ eY.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [hp, Category.assoc, Iso.inv_hom_id_assoc]
  have hs (Z : SmoothSite (Spec (CommRingCat.of k))) :
      (productBaseIso Z).inv ≫ SmoothSite.productMap (𝟙 Z) c = nativeAffineSection (.of k) Z a := by
    change productLift (𝟙 Z) (toBase Z) ≫ SmoothSite.productMap (𝟙 Z) c =
      productLift (𝟙 Z) (toBase Z ≫ c)
    apply product_hom_ext
    · simp only [Category.assoc, productMap_fst, Category.comp_id, productLift_fst]
    · simp only [Category.assoc, productMap_snd, productLift_snd_assoc, productLift_snd]
  have hg (Z : SmoothSite (Spec (CommRingCat.of k))) :
      γ (nativeAffineSection (.of k) Z a) =
        ((graphFunctor k).mapIso (productBaseIso Z)).inv ≫
          (parameterProductMap c).app (Cor.mk Z) := by
    change _ = γ (productBaseIso Z).inv ≫ γ (SmoothSite.productMap (𝟙 Z) c)
    rw [← Functor.map_comp, hs]
  rw [hg X, hg Y, Category.assoc, ← (parameterProductMap c).naturality α,
    ← Category.assoc, hi, Category.assoc]

end AlgebraicGeometry.Cor
