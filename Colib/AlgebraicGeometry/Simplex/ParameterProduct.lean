/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation

/-!
# Ordinary singular chains and a smooth parameter

The literal permutation of the parameter and the algebraic simplex commutes
with maps in the smooth source and in the simplex. The comparison therefore
acts on the native alternating-face complex with its original differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry AlgebraicTopology
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- Inserting the unit before permuting the last two factors inserts the unit
in the last factor after the permutation. -/
theorem productMap_unitSection_comp_productSwapLast {S : Scheme.{u}}
    (X D : SmoothSite S) :
    productMap (unitSection.app X) (𝟙 D) ≫ productSwapLast X (multiplicativeGroupObject S) D =
      unitSection.app (product X D) := by
  let T := multiplicativeGroupObject S
  let e : X ⟶ product X T := productLift (𝟙 X) (toBase X ≫ torusOne S)
  change productMap e (𝟙 D) ≫ productSwapLast X T D =
    productLift (𝟙 (product X D)) (toBase (product X D) ≫ torusOne S)
  apply product_hom_ext
  · rw [Category.assoc, productSwapLast_fst, ← productMap_comp, Category.id_comp]
    have he : e ≫ productFst X T = 𝟙 X := productLift_fst _ _
    rw [he, productMap_id, productLift_fst]
  · rw [Category.assoc, productSwapLast_snd, productMap_fst_assoc, productLift_snd,
      productLift_snd, comp_toBase_assoc]

end AlgebraicGeometry.Scheme.SmoothSite.Contraction

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R] {A : Type v} [Category.{w} A]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of R))
local notation "Psh" => Smᵒᵖ ⥤ A

/-- Reindex ordinary presheaves along the actual smooth parameter product. -/
abbrev parameterReindex (T : Sm) : Psh ⥤ Psh :=
  (Functor.whiskeringLeft Smᵒᵖ Smᵒᵖ A).obj (SmoothSite.Contraction.parameterProduct T).op

/-- The coordinate swap gives a simplicial comparison of the two parameter orders. -/
def simplicialPresheafParameterIso (T : Sm) (P : Psh) :
    simplicialPresheaf R ((parameterReindex R T).obj P) ≅
      ((SimplicialObject.whiskering Psh Psh).obj (parameterReindex R T)).obj
        (simplicialPresheaf R P) :=
  NatIso.ofComponents
    (fun n ↦ NatIso.ofComponents
      (fun U ↦ P.mapIso (SmoothSite.productSwapLastIso U.unop T
        ((cosimplicialSmoothSite R).obj n.unop)).op)
      (by
        intro U V f
        let D := (cosimplicialSmoothSite R).obj n.unop
        change P.map (SmoothSite.productMap (SmoothSite.productMap f.unop (𝟙 D)) (𝟙 T)).op ≫
            P.map (SmoothSite.productSwapLast V.unop T D).op =
          P.map (SmoothSite.productSwapLast U.unop T D).op ≫
            P.map (SmoothSite.productMap (SmoothSite.productMap f.unop (𝟙 T)) (𝟙 D)).op
        simp only [← P.map_comp, ← op_comp]
        exact congrArg (fun g ↦ P.map g.op)
          (SmoothSite.productSwapLast_naturality V.unop T D f.unop (𝟙 T) (𝟙 D)).symm))
    (by
      intro n m g
      apply NatTrans.ext
      funext U
      let D := (cosimplicialSmoothSite R).obj n.unop
      let E := (cosimplicialSmoothSite R).obj m.unop
      let d : E ⟶ D := (cosimplicialSmoothSite R).map g.unop
      change P.map (SmoothSite.productMap (SmoothSite.productMap (𝟙 U.unop) d) (𝟙 T)).op ≫
          P.map (SmoothSite.productSwapLast U.unop T E).op =
        P.map (SmoothSite.productSwapLast U.unop T D).op ≫
          P.map (SmoothSite.productMap (𝟙 (SmoothSite.product U.unop T)) d).op
      have h := SmoothSite.productSwapLast_naturality U.unop T E (𝟙 U.unop) (𝟙 T) d
      rw [SmoothSite.productMap_id] at h
      simp only [← P.map_comp, ← op_comp]
      exact congrArg (fun f ↦ P.map f.op) h.symm)

variable [Preadditive A]

/-- Ordinary singular chains commute with the actual smooth parameter product
by the coordinate permutation on each algebraic simplex. -/
def singularChainsParameterIso (T : Sm) (P : Psh) :
    (singularChainsFunctor R).obj ((parameterReindex R T).obj P) ≅
      (((parameterReindex R (A := A) T).mapHomologicalComplex (.down ℕ)).obj
        ((singularChainsFunctor R).obj P)) :=
  (alternatingFaceMapComplex Psh).mapIso (simplicialPresheafParameterIso R T P) ≪≫
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso (parameterReindex R T)).app
      (simplicialPresheaf R P)).symm

/-- The chain comparison uses pullback along the literal parameter swap. -/
@[simp]
theorem singularChainsParameterIso_hom_f_app (T : Sm) (P : Psh) (n : ℕ) (U : Sm) :
    ((singularChainsParameterIso R T P).hom.f n).app (op U) =
      P.map (SmoothSite.productSwapLast U T (smoothSiteObj R n)).op := by
  change P.map (SmoothSite.productSwapLast U T (smoothSiteObj R n)).op ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- A coefficient map into the parameter product induces the ordinary chain map. -/
def singularChainsParameterMap (T : Sm) {P Q : Psh} (η : P ⟶ (parameterReindex R T).obj Q) :
    (singularChainsFunctor R).obj P ⟶
      ((parameterReindex R T).mapHomologicalComplex (.down ℕ)).obj
        ((singularChainsFunctor R).obj Q) :=
  (singularChainsFunctor R).map η ≫ (singularChainsParameterIso R T Q).hom

/-- Apply the original coefficient map on simplices and pull back along the swap. -/
theorem singularChainsParameterMap_f_app (T : Sm) {P Q : Psh}
    (η : P ⟶ (parameterReindex R T).obj Q) (n : ℕ) (U : Sm) :
    ((singularChainsParameterMap R T η).f n).app (op U) =
      η.app (op (SmoothSite.product U (smoothSiteObj R n))) ≫
        Q.map (SmoothSite.productSwapLast U T (smoothSiteObj R n)).op := by
  simp only [singularChainsParameterMap, HomologicalComplex.comp_f, NatTrans.comp_app,
    singularChainsFunctor_map_f_app, singularChainsParameterIso_hom_f_app]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of R))

/-- Coefficient maps vanishing at parameter one give chain maps whose restriction
along the actual unit section vanishes degreewise. -/
theorem singularChainsParameterMap_f_app_unit {P Q : Psh}
    (η : P ⟶ (parameterReindex R Gₘ).obj Q)
    (hη : ∀ U : Sm, η.app (op U) ≫ Q.map (SmoothSite.Contraction.unitSection.app U).op = 0)
    (n : ℕ) (U : Sm) :
    ((singularChainsParameterMap R Gₘ η).f n).app (op U) ≫
        (((singularChainsFunctor R).obj Q).X n).map
          (SmoothSite.Contraction.unitSection.app U).op = 0 := by
  rw [singularChainsParameterMap_f_app]
  change (η.app (op (SmoothSite.product U (smoothSiteObj R n))) ≫
    Q.map (SmoothSite.productSwapLast U Gₘ (smoothSiteObj R n)).op) ≫
    Q.map (SmoothSite.productMap (SmoothSite.Contraction.unitSection.app U)
      (𝟙 (smoothSiteObj R n))).op = 0
  rw [Category.assoc, ← Q.map_comp, ← op_comp,
    SmoothSite.Contraction.productMap_unitSection_comp_productSwapLast]
  exact hη _

end AlgebraicSimplex
