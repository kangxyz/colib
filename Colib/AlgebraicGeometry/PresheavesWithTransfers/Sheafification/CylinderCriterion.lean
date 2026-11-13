/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1ProjectionIso
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.DenseDetection
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Whole-cylinder lifting and homotopy invariance of Nisnevich sheafification

A lift into the unit image on the whole cylinder over a nonempty base open
gives injectivity of the zero-section restriction by dense detection. The
projection is consequently invertible on integral affine objects, and then
on the whole smooth site.

Adapted from `Motivic/Cohomology/A1/Sheafification/CylinderCriterion.lean`
at motivic@a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Lifting into the unit image over the whole affine cylinder of a nonempty base open. -/
def ModelWholeCylinderLifting (P : PresheafWithTransfers.{u + 1} k) : Prop :=
  ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk (affineLineCylinder.obj X))),
    ∃ (U : SmoothSite (Spec (.of k))) (j : U ⟶ X),
      IsOpenImmersion j.left ∧ Nonempty U.left ∧
      ∃ t : (nisnevichImage P).sections (Cor.mk (affineLineCylinder.obj U)),
        (nisnevichImageι P).hom.app (op (Cor.mk (affineLineCylinder.obj U))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (affineLineCylinder.map j)) g

private theorem cylinder_denseRange {U X : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) (hj : DenseRange j.left) :
    DenseRange (affineLineCylinder.map j).left := by
  let T := SmoothSite.additiveGroupObject (Spec (.of k))
  let p := (SmoothSite.productFst X T).left
  let H := affineLineCylinder_map_isPullback j
  have hr : Set.range (affineLineCylinder.map j).left = p ⁻¹' Set.range j.left := by
    rw [← H.isoPullback_hom_fst]
    change Set.range ((pullback.fst p j.left) ∘ H.isoPullback.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr H.isoPullback.hom.surjective,
      Set.image_univ, Scheme.Pullback.range_fst]
  change Dense (Set.range (affineLineCylinder.map j).left)
  rw [hr]
  let : Smooth p := inferInstanceAs (Smooth (pullback.fst X.hom T.hom))
  exact hj.preimage p.isOpenMap

/-- Dense detection and whole-cylinder lifting give injectivity of the actual
zero-section restriction on an integral affine base. -/
theorem nisnevichSheafify_sectionPullback_injective_of_modelWholeCylinderLifting
    (hD : IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Function.Injective (A1.sectionPullback (.of k)
      ((toPresheaf k).obj ((nisnevichSheafify k).obj P).obj) X 0) := by
  let F := (toPresheaf k).obj ((nisnevichSheafify k).obj P).obj
  let S := (toPresheaf k).obj (nisnevichImage P)
  let η : S ⟶ F := (toPresheaf k).map (nisnevichImageι P)
  apply (injective_iff_map_eq_zero _).mpr
  intro g hg
  obtain ⟨U, j, hj, hU, t, ht⟩ := hL X g
  let : IsOpenImmersion j.left := hj
  let : Nonempty U.left := hU
  have hjd : DenseRange j.left :=
    j.left.isOpenMap.denseRange_of_isPreirreducibleSpace j.left
  let c := affineLineCylinder.map j
  let : IsOpenImmersion c.left := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsOpenImmersion) (affineLineCylinder_map_isPullback j).flip inferInstance
  have ht' : η.app (op (affineLineCylinder.obj U)) t = F.map c.op g := ht
  have hsection : nativeAffineSection (.of k) U 0 ≫ c =
      j ≫ nativeAffineSection (.of k) X 0 := by
    apply SmoothSite.product_hom_ext <;>
      simp [nativeAffineSection, c, parameterProduct, Category.assoc]
  have hz : S.map (nativeAffineSection (.of k) U 0).op t = 0 := by
    have hm : Mono (η.app (op U)) :=
      inferInstanceAs (Mono ((nisnevichImageι P).hom.app (op (Cor.mk U))))
    apply (AddCommGrpCat.mono_iff_injective (η.app (op U))).mp hm
    rw [map_zero, η.naturality_apply, ht']
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
      hsection, op_comp, F.map_comp, ConcreteCategory.comp_apply]
    change F.map j.op (A1.sectionPullback (.of k) F X 0 g) = 0
    rw [hg, map_zero]
  have htzero : t = 0 := by
    have hS : A1.IsInvariant (.of k) S := nisnevichImage_isA1Invariant P hP
    have he := ConcreteCategory.congr_hom
      (A1.sectionPullback_projectionPullback (.of k) S hS U 0) t
    change A1.projectionPullback (.of k) S U (S.map (nativeAffineSection (.of k) U 0).op t) =
      t at he
    rw [hz, map_zero] at he
    exact he.symm
  apply nisnevichSheafify_section_eq_zero_of_dense_open_of_integralAffineLocalZero hD P hP c
    (cylinder_denseRange j hjd) g
  change F.map c.op g = 0
  rw [← ht', htzero, map_zero]

/-- The actual Nisnevich sheafification is HI from dense detection and
whole-cylinder lifting of its original sections. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/A1/Sheafification/CylinderCriterion.lean"
  "adaptation" "The literal affine-cylinder projection and the original sheafification"]
theorem nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting
    (hD : IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P) :
    ((nisnevichSheafify k).obj P).obj.IsA1Invariant := by
  let F := (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)
  let C : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
    ⟨affineLineCylinder.op ⋙ F.obj,
      parameterProduct_op_comp_isSheaf _ F.obj F.property⟩
  let φ : F ⟶ C := ⟨{
    app X := A1.projectionPullback (.of k) F.obj X.unop
    naturality := fun _ _ f ↦ A1.projectionPullback_naturality (.of k) F.obj f.unop }⟩
  have hφ : IsIso φ := by
    apply SmoothSite.isIso_of_integral_affine_app k
    intro X _ _
    let p := A1.projectionPullback (.of k) F.obj X
    let s := A1.sectionPullback (.of k) F.obj X 0
    have hs : Function.Injective s :=
      nisnevichSheafify_sectionPullback_injective_of_modelWholeCylinderLifting hD P hP hL X
    have hp : p ≫ s = 𝟙 _ := A1.projectionPullback_sectionPullback (.of k) F.obj X 0
    have hsp : s ≫ p = 𝟙 _ := by
      ext g
      apply hs
      exact ConcreteCategory.congr_hom hp (s g)
    exact ⟨⟨s, hp, hsp⟩⟩
  let : IsIso φ := hφ
  have : IsIso φ.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map φ))
  intro X
  change IsIso (φ.hom.app (op X))
  exact NatIso.isIso_app_of_isIso φ.hom (op X)

end AlgebraicGeometry.PresheafWithTransfers
