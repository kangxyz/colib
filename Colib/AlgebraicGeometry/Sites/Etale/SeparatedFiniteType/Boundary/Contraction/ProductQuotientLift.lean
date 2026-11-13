/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1PunctureBaseChange
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.CokernelLifting


/-! # Product projection on the original ambient cokernel of an étale chart

The map is the restriction of the actual cylinder projection map through
genuine étale excision. The quotient equation retains the original punctured
representatives. No closed-support identification on a later local quotient
lift is required.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Contraction/ProjectionExcision.lean`, blob
`6b1851c867bd40409269fda111eae3332f3aab4a`.
The product construction works over any ring. The local lift uses a specified
antecedent under the original-base quotient projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

section Product

variable {R : CommRingCat.{u}} {U E : SmoothSite (Spec R)} (j : U ⟶ E)

local notation "U₁" => Functor.obj SmoothSite.Contraction.affineLineCylinder U
local notation "E₁" => Functor.obj SmoothSite.Contraction.affineLineCylinder E
local notation "j₁" => SmoothSite.Contraction.affineLineCylinder.map j
local notation "πU" =>
  NatTrans.app (SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))) U
local notation "πE" =>
  NatTrans.app (SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))) E

/-- The direct images in the literal puncture/product square commute. -/
def a1PunctureProjectionDirectImageIso :
    directImage (πU).left ⋙ directImage j.left ≅
      directImage (j₁).left ⋙
        directImage (πE).left := by
  let : (baseChange (πE).left).IsContinuous
      (nisnevichTopology E.left) (nisnevichTopology (E₁).left) :=
    baseChange_isContinuous (S := E.left) (T := (E₁).left) (πE).left
  have := Functor.isContinuous_comp (baseChange j.left) (baseChange (πU).left)
    (nisnevichTopology E.left) (nisnevichTopology U.left) (nisnevichTopology (U₁).left)
  have := Functor.isContinuous_comp (baseChange (πE).left) (baseChange (j₁).left)
    (nisnevichTopology E.left) (nisnevichTopology (E₁).left) (nisnevichTopology (U₁).left)
  exact Functor.sheafPushforwardContinuousIso
    (a1PunctureProjectionBaseChangeIso j).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology E.left) (nisnevichTopology (U₁).left)

variable (G : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})

/-- Pullback of original punctured sections along the actual homotopy projection. -/
def a1PuncturedProjectionMap :
    (directImage j.left).obj ((restrict U AddCommGrpCat).obj G) ⟶
      (directImage (πE).left).obj
        ((directImage (j₁).left).obj
          ((restrict U₁ AddCommGrpCat).obj G)) :=
  (directImage j.left).map
    (restrictionToDirectImage G πU) ≫
    (a1PunctureProjectionDirectImageIso j).hom.app
      ((restrict U₁ AddCommGrpCat).obj G)

/-- The actual product pullback preserves the original ambient restriction relation. -/
theorem a1PuncturedProjectionMap_restriction :
    restrictionToDirectImage G j ≫ a1PuncturedProjectionMap j G =
      restrictionToDirectImage G πE ≫
        (directImage (πE).left).map
          (restrictionToDirectImage G j₁) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (G).obj.map ((restrictionProjection j).app V.unop).op ≫
      ((G).obj.map ((restrictionProjection πU).app
        ((baseChange j.left).obj V.unop)).op ≫
        (G).obj.map ((toSmoothSite U₁).map
          ((a1PunctureProjectionBaseChangeIso j).hom.app V.unop)).op) =
    (G).obj.map
      ((restrictionProjection πE).app V.unop).op ≫
      (G).obj.map ((restrictionProjection j₁).app
        ((baseChange (πE).left).obj V.unop)).op
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change ((a1PunctureProjectionBaseChangeIso j).hom.app V.unop).left ≫
      pullback.fst (pullback.snd V.unop.hom j.left)
        (πU).left ≫
      pullback.fst V.unop.hom j.left =
    pullback.fst (pullback.snd V.unop.hom (πE).left)
        (j₁).left ≫
      pullback.fst V.unop.hom (πE).left
  exact a1PunctureProjectionBaseChangeIso_fst j V.unop

/-- The actual ambient cokernel projection pullback for an original puncture.
This is the coefficient map needed by the ordinary localization sequence. -/
def a1AmbientProjectionMap :
    boundaryAmbientCokernel G j ⟶
      (directImage (πE).left).obj
        (boundaryAmbientCokernel G j₁) :=
  cokernel.desc (restrictionToDirectImage G j)
    (a1PuncturedProjectionMap j G ≫
      (directImage (πE).left).map
        (cokernel.π (restrictionToDirectImage G j₁))) (by
          rw [← Category.assoc, a1PuncturedProjectionMap_restriction, Category.assoc,
            ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero])

/-- The actual product map sends each unchanged punctured generator through
the original target cokernel projection. -/
@[reassoc (attr := simp)]
theorem a1AmbientProjectionMap_π :
    cokernel.π (restrictionToDirectImage G j) ≫ a1AmbientProjectionMap j G =
      a1PuncturedProjectionMap j G ≫
        (directImage (πE).left).map
          (cokernel.π (restrictionToDirectImage G j₁)) :=
  cokernel.π_desc _ _ _

/-- Once the original split-chart product equality has been established, the
native cokernel epimorphism lifts it after a genuine pointed base refinement.
The original marking point, quotient and product restriction remain unchanged.
No support-unit assertion is made on the refined ambient neighborhood. -/
theorem exists_pointed_a1_product_quotient_lift
    (Φ : (nisnevichTopology E.left).Point.{u + 1})
    (V : EtaleSeparatedFiniteType E.left) (v : Φ.fiber.obj V)
    (c₀ : (boundaryAmbientCokernel G j).obj.obj (op V))
    (c₁ : (boundaryAmbientCokernel G j₁).obj.obj
      (op ((baseChange (πE).left).obj V)))
    (hc : (a1AmbientProjectionMap j G).hom.app
      (op V) c₀ = c₁) :
    ∃ (W : EtaleSeparatedFiniteType E.left) (a : W ⟶ V) (w : Φ.fiber.obj W)
      (t : ((directImage j.left).obj ((restrict U AddCommGrpCat).obj G)).obj.obj (op W)),
      Φ.fiber.map a w = v ∧
      (cokernel.π (restrictionToDirectImage G j₁)).hom.app
          (op ((baseChange (πE).left).obj W))
          ((a1PuncturedProjectionMap j G).hom.app
            (op W) t) =
        (boundaryAmbientCokernel G j₁).obj.map
          ((baseChange (πE).left).map a).op c₁ := by
  let r := restrictionToDirectImage G j
  have hzero : cokernel.π (cokernel.π r) = 0 :=
    (isZero_cokernel_of_epi (cokernel.π r)).eq_of_tgt _ _
  obtain ⟨W, a, w, t, ha, ht⟩ := exists_pointed_local_lift_of_cokernel_germ_zero
    Φ (cokernel.π r) V v c₀ (by simp [hzero])
  refine ⟨W, a, w, t, ha, ?_⟩
  have hπ := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op W))
      (a1AmbientProjectionMap_π j G)) t
  change (a1AmbientProjectionMap j G).hom.app
      (op W) ((cokernel.π r).hom.app (op W) t) = _ at hπ
  rw [ht] at hπ
  have hn := ConcreteCategory.congr_hom
    ((a1AmbientProjectionMap j G).hom.naturality a.op) c₀
  change (a1AmbientProjectionMap j G).hom.app
      (op W) ((boundaryAmbientCokernel G j).obj.map a.op c₀) =
    (boundaryAmbientCokernel G j₁).obj.map
      ((baseChange (πE).left).map a).op
      ((a1AmbientProjectionMap j G).hom.app
        (op V) c₀) at hn
  rw [hc] at hn
  exact hπ.symm.trans hn

end Product

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
