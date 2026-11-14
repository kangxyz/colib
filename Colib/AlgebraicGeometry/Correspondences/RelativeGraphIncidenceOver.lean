/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphIncidenceFactor
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphOver

/-! # Explicit factorization of the original incidence outer map -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)

/-- The native incidence outer map factors through the actual closed relative
 graph by its canonical forgetful projection. No pointwise lifting is used. -/
theorem incidenceMap_factor_over (s : V.left)
    (z : pullback (C := Scheme) U.hom Y.hom) :
    let m := correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
      (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
      (ambientLift k U Y z)
    (m ≫ ambientForget k) ≫ ambientOver k (Y := Y) f = m := by
  dsimp only
  apply pullback.hom_ext
  · simp [ambientForget, ambientOver, graphTargetMap, Category.assoc,
      SmoothSite.product_hom]
  · apply pullback.hom_ext
    · simp only [Functor.const_obj_obj, Functor.id_obj, SmoothSite.product_left,
        SmoothSite.product_hom, ambientForget, graphTargetMap, SmoothSite.productSnd,
        SmoothSite.homMk_left, ambientOver, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, MorphismProperty.Comma.comp_hom, Comma.comp_left,
        Category.comp_id, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, ambientLift_snd_assoc, limit.lift_π_assoc, cospan_left,
        correspondenceIncidenceMap_fst_assoc, correspondenceIncidenceMap_snd]
      have h := (incidence_retained_source_eq k f s z).symm
      simp only [correspondenceIncidenceMap_fst_assoc,
        correspondenceIncidenceMap_snd_assoc, SmoothSite.product_hom] at h
      convert h using 1
    · simp [ambientForget, ambientOver, graphTargetMap, Category.assoc,
        SmoothSite.product_hom, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, SmoothSite.productSnd]

end AlgebraicGeometry.Cor.RelativeGraph
