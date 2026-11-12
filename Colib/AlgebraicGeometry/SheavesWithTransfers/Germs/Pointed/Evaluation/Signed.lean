/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Evaluation.SectionCompatibility
public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-! # Signed correspondence evaluation on the original Nisnevich point fibers

This is the additive extension of the geometrically constructed generator action.
Composition is not assumed in this construction.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- Extend the geometrically constructed action using the actual native integer coefficients. -/
def correspondenceGermHom (x : X.left) :
    (Cor.mk X ⟶ Cor.mk Y) →+
      ((∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) →+
        (SmoothSite.nisnevichPointFiberCocone X x F).pt) :=
  liftFiniteCorrespondence X.hom Y.hom (fun A hA => generatorGermHom k P hP A hA x)

theorem correspondenceGermHom_single
    (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (c : ℤ) (x : X.left) :
    correspondenceGermHom k P hP x (singleFiniteCorrespondence X.hom Y.hom A hA c) =
      c • generatorGermHom k P hP A hA x :=
  liftFiniteCorrespondence_single X.hom Y.hom _ A hA c

theorem correspondenceGermHom_cycle
    (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (x : X.left) :
    correspondenceGermHom k P hP x (singleFiniteCorrespondence X.hom Y.hom A hA 1) =
      generatorGermHom k P hP A hA x := by
  rw [correspondenceGermHom_single, one_zsmul]

/-- The support and signed coefficients are those of the original algebraic cycle. -/
theorem correspondenceGermHom_apply
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    correspondenceGermHom k P hP x δ a =
      ∑ A : δ.property.1.toFinset, δ.val A.val •
        generatorGermEvaluation k P A.val
          (δ.property.2 A.val (δ.property.1.mem_toFinset.mp A.property)) x a := by
  classical
  conv_lhs => rw [finiteCorrespondence_eq_sum_signedSingles X.hom Y.hom δ]
  simp only [map_sum, AddMonoidHom.finsetSum_apply, correspondenceGermHom_single,
    AddMonoidHom.zsmul_apply]
  rfl

/-- Signed evaluation recovers the original transfer on actual global sections. -/
theorem correspondenceGermHom_section
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left) (s : P.sections (Cor.mk Y)) :
    correspondenceGermHom k P hP x δ
        (fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} F Y y s) =
      SmoothSite.sectionToNisnevichPoint.{u, 0} F X x (P.transfer δ s) := by
  let a := fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} F Y y s
  let e : (Cor.mk X ⟶ Cor.mk Y) →+ P.sections (Cor.mk X) :=
    { toFun := fun γ => P.transfer γ s
      map_zero' := by simp
      map_add' := fun γ η => by simp only [transfer_add, AddCommGrpCat.hom_add_apply] }
  let l : (Cor.mk X ⟶ Cor.mk Y) →+
      (SmoothSite.nisnevichPointFiberCocone X x F).pt :=
    (AddMonoidHom.eval a).comp (correspondenceGermHom k P hP x)
  let r := (SmoothSite.sectionToNisnevichPoint.{u, 0} F X x).hom.comp e
  have hlr : l = r := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro A hA
    change correspondenceGermHom k P hP x
      (singleFiniteCorrespondence X.hom Y.hom A hA 1) a = _
    rw [correspondenceGermHom_cycle]
    exact generatorGermEvaluation_section k P hP A hA x s
  exact DFunLike.congr_fun hlr δ

end AlgebraicGeometry.PresheafWithTransfers
