/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterSwap.Support
public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph

/-!
# Parameter exchange of the native iterated exterior point

The whole support maps are identified through the permutation of the two
parameter pullbacks. Transport of their generic points gives the actual
twice-extended prime in the swapped ambient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

private theorem productSwapLast_left_fst_fst {S : Scheme.{u}} (X T V : SmoothSite S) :
    (SmoothSite.productSwapLastIso X T V).hom.left ≫
        pullback.fst (SmoothSite.product X V).hom T.hom ≫ pullback.fst X.hom V.hom =
      pullback.fst (SmoothSite.product X T).hom V.hom ≫ pullback.fst X.hom T.hom := by
  have h : SmoothSite.productSwapLast X T V ≫
      SmoothSite.productFst (SmoothSite.product X V) T ≫ SmoothSite.productFst X V =
        SmoothSite.productFst (SmoothSite.product X T) V ≫ SmoothSite.productFst X T := by
    rw [SmoothSite.productSwapLast_fst_assoc, SmoothSite.productMap_fst]
  exact congrArg (fun f => f.left) h

private theorem productSwapLast_left_fst_snd {S : Scheme.{u}} (X T V : SmoothSite S) :
    (SmoothSite.productSwapLastIso X T V).hom.left ≫
        pullback.fst (SmoothSite.product X V).hom T.hom ≫ pullback.snd X.hom V.hom =
      pullback.snd (SmoothSite.product X T).hom V.hom := by
  have h : SmoothSite.productSwapLast X T V ≫
      SmoothSite.productFst (SmoothSite.product X V) T ≫ SmoothSite.productSnd X V =
        SmoothSite.productSnd (SmoothSite.product X T) V := by
    rw [SmoothSite.productSwapLast_fst_assoc, SmoothSite.productMap_snd, Category.comp_id]
  exact congrArg (fun f => f.left) h

private theorem productSwapLast_left_snd {S : Scheme.{u}} (X T V : SmoothSite S) :
    (SmoothSite.productSwapLastIso X T V).hom.left ≫
        pullback.snd (SmoothSite.product X V).hom T.hom =
      pullback.fst (SmoothSite.product X T).hom V.hom ≫ pullback.snd X.hom T.hom :=
  congrArg (fun f => f.left) (SmoothSite.productSwapLast_snd X T V)

variable {k : Type u} [Field k] (X Y T V : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral V.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation "W" => integralComponentAt z
local notation "Xₜ" => SmoothSite.product X T
local notation "Yₜ" => SmoothSite.product Y T
local notation "Xᵥ" => SmoothSite.product X V
local notation "Yᵥ" => SmoothSite.product Y V
local notation "Xₜᵥ" => SmoothSite.product Xₜ V
local notation "Yₜᵥ" => SmoothSite.product Yₜ V
local notation "Xᵥₜ" => SmoothSite.product Xᵥ T
local notation "Yᵥₜ" => SmoothSite.product Yᵥ T
local notation "zₜ" => nativeExteriorPoint X Y T z hz
local notation "zᵥ" => nativeExteriorPoint X Y V z hz
local notation "hₜ" => nativeExteriorPoint_admissible X Y T z hz
local notation "hᵥ" => nativeExteriorPoint_admissible X Y V z hz
local notation "b₀" => exteriorSupportSourceProjection X Y W ≫ X.hom
local notation "Dₜᵥ" => pullback (C := Scheme) (pullback.fst b₀ T.hom ≫ b₀) V.hom
local notation "Dᵥₜ" => pullback (C := Scheme) (pullback.fst b₀ V.hom ≫ b₀) T.hom
local notation "Iₜᵥ" => nativeExteriorIteratedInclusion X Y T V z hz
local notation "Iᵥₜ" => nativeExteriorIteratedInclusion X Y V T z hz
local notation "σ" => pullbackParameterProductIso b₀ V.hom T.hom
local notation "σX" => SmoothSite.productSwapLastIso X T V
local notation "σY" => SmoothSite.productSwapLastIso Y T V
set_option quotPrecheck false in
local notation "M" => (SmoothSite.productMap (σX).hom (σY).hom).left

set_option maxHeartbeats 600000 in
-- The six projections reduce the two different presentations of the iterated product.
/-- The actual full support inclusion commutes with the two ambient permutations. -/
theorem nativeExteriorIteratedInclusion_swap : Iₜᵥ ≫ M = (σ).hom ≫ Iᵥₜ := by
  have hfst : M ≫ pullback.fst (Xᵥₜ).hom (Yᵥₜ).hom =
      pullback.fst (Xₜᵥ).hom (Yₜᵥ).hom ≫ (σX).hom.left :=
    congrArg (fun f => f.left) (SmoothSite.productMap_fst (σX).hom (σY).hom)
  have hsnd : M ≫ pullback.snd (Xᵥₜ).hom (Yᵥₜ).hom =
      pullback.snd (Xₜᵥ).hom (Yₜᵥ).hom ≫ (σY).hom.left :=
    congrArg (fun f => f.left) (SmoothSite.productMap_snd (σX).hom (σY).hom)
  apply pullback.hom_ext (f := (Xᵥₜ).hom) (g := (Yᵥₜ).hom)
  · simp only [Category.assoc, hfst]
    apply pullback.hom_ext (f := (Xᵥ).hom) (g := T.hom)
    · apply pullback.hom_ext (f := X.hom) (g := V.hom)
      · simp only [Category.assoc, productSwapLast_left_fst_fst,
          nativeExteriorIteratedInclusion_source_fst_assoc, exteriorIdentitySource_fst,
          pullbackParameterProductIso_hom_first_assoc]
      · simp only [Category.assoc, productSwapLast_left_fst_snd,
          nativeExteriorIteratedInclusion_source_snd,
          nativeExteriorIteratedInclusion_source_fst_assoc, exteriorIdentitySource_snd,
          pullbackParameterProductIso_hom_second]
    · simp only [Category.assoc, productSwapLast_left_snd,
        nativeExteriorIteratedInclusion_source_fst_assoc, exteriorIdentitySource_snd,
        nativeExteriorIteratedInclusion_source_snd, pullbackParameterProductIso_hom_parameter]
  · simp only [Category.assoc, hsnd]
    apply pullback.hom_ext (f := (Yᵥ).hom) (g := T.hom)
    · apply pullback.hom_ext (f := Y.hom) (g := V.hom)
      · simp only [Category.assoc, productSwapLast_left_fst_fst,
          nativeExteriorIteratedInclusion_target_fst_assoc, exteriorIdentityTarget_fst,
          pullbackParameterProductIso_hom_first_assoc]
      · simp only [Category.assoc, productSwapLast_left_fst_snd,
          nativeExteriorIteratedInclusion_target_snd,
          nativeExteriorIteratedInclusion_target_fst_assoc, exteriorIdentityTarget_snd,
          pullbackParameterProductIso_hom_second]
    · simp only [Category.assoc, productSwapLast_left_snd,
        nativeExteriorIteratedInclusion_target_fst_assoc, exteriorIdentityTarget_snd,
        nativeExteriorIteratedInclusion_target_snd, pullbackParameterProductIso_hom_parameter]

private theorem nativeExteriorPoint_eq_supportGeneric :
    letI := nativeExteriorSupport_isIntegral X Y T z hz
    nativeExteriorPoint X Y T z hz =
      exteriorIdentityInclusion X Y T W (genericPoint (exteriorIdentitySupport X Y T W)) := by
  let : IsFinite (exteriorSupportSourceProjection X Y W) := hz.1
  let : IsIntegral (exteriorIdentitySupport X Y T W) := nativeExteriorSupport_isIntegral X Y T z hz
  let e := exteriorIdentityInclusion X Y T W
  let : IsIntegral e.ker.subscheme := nativeExteriorImage_isIntegral X Y T z hz
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  have h := congrArg e.imageι (genericPoint_eq_of_isOpenImmersion e.toImage)
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] at h
  exact h.symm

include hz in
private theorem nativeExteriorIteratedProduct_isIntegral : IsIntegral Dₜᵥ := by
  let : IsIntegral (exteriorIdentitySupport Xₜ Yₜ V (integralComponentAt zₜ)) :=
    nativeExteriorSupport_isIntegral Xₜ Yₜ V zₜ hₜ
  exact IsIntegral.of_isIso (nativeExteriorIteratedSupportIso X Y T V z hz).inv

private theorem nativeExteriorIteratedInclusion_genericPoint :
    letI := nativeExteriorIteratedProduct_isIntegral X Y T V z hz
    Iₜᵥ (genericPoint Dₜᵥ) = nativeExteriorPoint Xₜ Yₜ V zₜ hₜ := by
  let : IsIntegral Dₜᵥ := nativeExteriorIteratedProduct_isIntegral X Y T V z hz
  let : IsIntegral (exteriorIdentitySupport Xₜ Yₜ V (integralComponentAt zₜ)) :=
    nativeExteriorSupport_isIntegral Xₜ Yₜ V zₜ hₜ
  let e := nativeExteriorIteratedSupportIso X Y T V z hz
  let j := exteriorIdentityInclusion Xₜ Yₜ V (integralComponentAt zₜ)
  change j (e.hom (genericPoint Dₜᵥ)) = _
  exact (congrArg j (genericPoint_eq_of_isOpenImmersion e.hom)).trans
    (nativeExteriorPoint_eq_supportGeneric Xₜ Yₜ V zₜ hₜ).symm

/-- The actual twice-extended prime point is carried to the twice-extended
prime in the opposite parameter order. -/
theorem nativeExteriorIteratedPoint_swap :
    M (nativeExteriorPoint Xₜ Yₜ V zₜ hₜ) = nativeExteriorPoint Xᵥ Yᵥ T zᵥ hᵥ := by
  let : IsIntegral Dₜᵥ := nativeExteriorIteratedProduct_isIntegral X Y T V z hz
  let : IsIntegral Dᵥₜ := nativeExteriorIteratedProduct_isIntegral X Y V T z hz
  have h := congrArg
    (fun f : Dₜᵥ ⟶ pullback (Xᵥₜ).hom (Yᵥₜ).hom => f (genericPoint Dₜᵥ))
    (nativeExteriorIteratedInclusion_swap X Y T V z hz)
  change M (Iₜᵥ (genericPoint Dₜᵥ)) = Iᵥₜ ((σ).hom (genericPoint Dₜᵥ)) at h
  calc
    _ = M (Iₜᵥ (genericPoint Dₜᵥ)) := congrArg M
      (nativeExteriorIteratedInclusion_genericPoint X Y T V z hz).symm
    _ = Iᵥₜ ((σ).hom (genericPoint Dₜᵥ)) := h
    _ = Iᵥₜ (genericPoint Dᵥₜ) :=
      congrArg Iᵥₜ (genericPoint_eq_of_isOpenImmersion (σ).hom)
    _ = _ := nativeExteriorIteratedInclusion_genericPoint X Y V T z hz

end Stacks.Chow
