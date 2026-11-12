/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusParameter
public import Colib.AlgebraicGeometry.Simplex.ParameterProduct
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Presheaf
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products

/-!
# The reduced torus parameter product on ordinary singular chains

The actual signed parameter product induces a map on the underlying ordinary
singular complexes. Its components use the original coefficient map followed
by the coordinate permutation, and its restriction at parameter one is zero.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "Smₖ" => SmoothSite Sₖ
local notation "Torus₀" q:max => Functor.obj (toPresheaf k) (reducedTorus k q)

/-- Graph restriction of the actual parameter product on reduced transfer tori. -/
def ordinaryReducedTorusParameterProduct (q : ℕ) :
    Torus₀ q ⟶ (AlgebraicSimplex.parameterReindex k Gₘ).obj (Torus₀ (q + 1)) :=
  (toPresheaf k).map (reducedTorusParameterProduct k q) ≫
    (withParameterUnderlyingIso (reducedTorus k (q + 1)) Gₘ).hom

/-- The ordinary map keeps the components of the original signed correspondence map. -/
theorem ordinaryReducedTorusParameterProduct_app (q : ℕ) (U : Smₖ) :
    (ordinaryReducedTorusParameterProduct k q).app (op U) =
      (reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) := by
  simp only [ordinaryReducedTorusParameterProduct, NatTrans.comp_app, toPresheaf_map_app,
    withParameterUnderlyingIso_hom_app, Category.comp_id]

private theorem ordinaryReducedTorusParameterProduct_app_unit (q : ℕ) (U : Smₖ) :
    (ordinaryReducedTorusParameterProduct k q).app (op U) ≫
      (Torus₀ (q + 1)).map (SmoothSite.Contraction.unitSection.app U).op = 0 := by
  let Q := Torus₀ (q + 1)
  have h := congrArg (fun f ↦ f.hom.app (op (Cor.mk U)))
    (reducedTorusParameterProduct_parameterPullback_one k q)
  change (reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) ≫
      Q.map (SmoothSite.productMap (𝟙 U) (SmoothSite.torusOne Sₖ)).op = 0 at h
  rw [ordinaryReducedTorusParameterProduct_app]
  change (reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) ≫
      Q.map (SmoothSite.Contraction.unitSection.app U).op = 0
  rw [← SmoothSite.Contraction.baseProduct_unit, op_comp, Q.map_comp,
    ← Category.assoc, h, zero_comp]

/-- The ordinary singular chain map induced by multiplication by the actual
parameter coordinate on reduced transfer tori. -/
def reducedTorusSingularParameterProduct (q : ℕ) :
    (AlgebraicSimplex.singularChainsFunctor k).obj (Torus₀ q) ⟶
      ((AlgebraicSimplex.parameterReindex k (A := AddCommGrpCat.{u + 1}) Gₘ).mapHomologicalComplex
        (.down ℕ)).obj ((AlgebraicSimplex.singularChainsFunctor k).obj (Torus₀ (q + 1))) :=
  AlgebraicSimplex.singularChainsParameterMap k Gₘ (ordinaryReducedTorusParameterProduct k q)

/-- In every degree the ordinary chain map uses the original parameter product
on simplices and pullback along the literal last-factor swap. -/
theorem reducedTorusSingularParameterProduct_f_app (q n : ℕ) (U : Smₖ) :
    ((reducedTorusSingularParameterProduct k q).f n).app (op U) =
      (reducedTorusParameterProduct k q).hom.app
          (op (Cor.mk (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k n)))) ≫
        (Torus₀ (q + 1)).map
          (SmoothSite.productSwapLast U Gₘ (AlgebraicSimplex.smoothSiteObj k n)).op := by
  rw [reducedTorusSingularParameterProduct, AlgebraicSimplex.singularChainsParameterMap_f_app,
    ordinaryReducedTorusParameterProduct_app]

/-- Restriction of the actual ordinary chain map at parameter one vanishes in every degree. -/
theorem reducedTorusSingularParameterProduct_f_unit (q n : ℕ) :
    (reducedTorusSingularParameterProduct k q).f n ≫
      SmoothSite.Contraction.unit
        (((AlgebraicSimplex.singularChainsFunctor k).obj (Torus₀ (q + 1))).X n) = 0 := by
  apply NatTrans.ext
  funext U
  exact AlgebraicSimplex.singularChainsParameterMap_f_app_unit k
    (ordinaryReducedTorusParameterProduct k q) (ordinaryReducedTorusParameterProduct_app_unit k q)
    n U.unop

end AlgebraicGeometry.PresheafWithTransfers
