/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.Util.References

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DerivedPushforwardTwist
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeMateUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension

/-! # The canonical derived adjunction unit for a projective line

The unit is invertible on the structure sheaf, by the actual projective-space coefficient map.
The canonical projection-formula morphism and the tensor-unit constraints give invertibility
on all perfect complexes, by the adjunction tensor identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  CategoryTheory.sheafCompose Stacks.SheafOfModules.Tensor.ringSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.projectiveSpaceOver

universe u

attribute [local instance 2000] HasDerivedCategory.standard

private abbrev D (X : RingedSpace.{u, u}) :=
  DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))

private abbrev U (X : RingedSpace.{u, u}) : D X :=
  (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
    (_root_.SheafOfModules.unit (structureSheafRing X))

private theorem unit_isIso_of_structure_unit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : D Y) (hK : AlgebraicGeometry.RingedSpace.IsPerfect (X := Y) K)
    (hU : IsIso ((derivedAdjunction f).unit.app (U Y))) :
    IsIso ((derivedAdjunction f).unit.app K) := by
  let L := derivedPullback f
  let R := derivedPushforward f
  let adj := derivedAdjunction f
  let A := Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)
  let B := Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)
  let a := pullbackTensorComparison f
  let v : L.obj (U Y) ≅ U X := Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f
  let e : A.obj (U Y, K) ≅ K := Stacks.RingedSpace.derivedTensorLeftUnitIso Y K
  let m : A.obj (U Y, K) ⟶ R.obj (B.obj (U X, L.obj K)) :=
    A.map (adj.homEquiv _ _ v.hom ×ₘ 𝟙 K) ≫ projectionFormulaMap f (U X) K
  let w : L.obj (A.obj (U Y, K)) ⟶ B.obj (U X, L.obj K) :=
    a.app (U Y, K) ≫ B.map (v.hom ×ₘ 𝟙 (L.obj K))
  have hv : IsIso (adj.homEquiv _ _ v.hom) := by
    rw [Adjunction.homEquiv_unit]
    exact IsIso.comp_isIso' hU (R.mapIso v).isIso_hom
  let : IsIso (adj.homEquiv _ _ v.hom ×ₘ 𝟙 K) :=
    (CategoryTheory.isIso_prod_iff _ _).2 ⟨hv, inferInstance⟩
  let : IsIso (A.map (adj.homEquiv _ _ v.hom ×ₘ 𝟙 K)) :=
    (A.mapIso (asIso (adj.homEquiv _ _ v.hom ×ₘ 𝟙 K))).isIso_hom
  let : IsIso (projectionFormulaMap f (U X) K) :=
    Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isPerfect f (U X) K hK
  have hm : IsIso m := by dsimp [m]; infer_instance
  have hw : IsIso w := by
    let : IsIso (a.app (U Y, K)) :=
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).app _).isIso_hom
    have hvprod : IsIso (v.hom ×ₘ 𝟙 (L.obj K)) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨v.isIso_hom, inferInstance⟩
    let : IsIso (B.map (v.hom ×ₘ 𝟙 (L.obj K))) := (B.mapIso (asIso _)).isIso_hom
    dsimp [w]
    infer_instance
  have hmate : m = adj.unit.app (A.obj (U Y, K)) ≫ R.map w := by
    let q := (U Y, K)
    let v' : (L.obj (U Y), L.obj K) ⟶ (U X, L.obj K) := v.hom ×ₘ 𝟙 (L.obj K)
    have h₁ := adjunctionTensorMap_natural adj A B a v.hom (𝟙 K)
    have h₂ := adjunctionTensorMap_unit adj A B a (U Y) K
    have hu : adj.homEquiv _ _ v.hom = adj.unit.app (U Y) ≫ R.map v.hom :=
      adj.homEquiv_unit _ _ _
    have ht : (adj.homEquiv _ _ v.hom ×ₘ 𝟙 K) =
        (adj.unit.app (U Y) ×ₘ 𝟙 K) ≫ (R.map v.hom ×ₘ 𝟙 K) := by
      rw [hu]
      apply CategoryTheory.Prod.hom_ext <;> simp
    dsimp only [m, w]
    change A.map (adj.homEquiv _ _ v.hom ×ₘ 𝟙 K) ≫
      adjunctionTensorMap adj A B a (U X) K = adj.unit.app (A.obj q) ≫
        R.map (a.app q ≫ B.map v')
    rw [ht, A.map_comp, Category.assoc, h₁, ← Category.assoc, h₂,
      Adjunction.homEquiv_unit, Category.assoc, ← R.map_comp, L.map_id]
  have hu : IsIso (adj.unit.app (A.obj (U Y, K))) := by
    let : IsIso (R.map w) := (R.mapIso (@asIso _ _ _ _ w hw)).isIso_hom
    let : IsIso (adj.unit.app (A.obj (U Y, K)) ≫ R.map w) := by
      rw [← hmate]
      exact hm
    exact IsIso.of_isIso_comp_right (adj.unit.app (A.obj (U Y, K))) (R.map w)
  have he := adj.unit.naturality e.hom
  change e.hom ≫ adj.unit.app K = adj.unit.app (A.obj (U Y, K)) ≫
    (L ⋙ R).map e.hom at he
  let : IsIso (e.hom ≫ adj.unit.app K) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom (adj.unit.app K)

private theorem structureSheaf_hom_comm (X : Scheme.{u})
    (a b : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf) : a ≫ b = b ≫ a := by
  ext V
  have hF : ∀ (F : Γ(X, V.unop) →ₗ[Γ(X, V.unop)] Γ(X, V.unop)) (x : Γ(X, V.unop)),
      F x = x * F 1 := fun F x => by
    calc
      F x = F (x • (1 : Γ(X, V.unop))) := by simp [smul_eq_mul]
      _ = x • F 1 := F.map_smul x 1
      _ = x * F 1 := rfl
  let Fa : Γ(X, V.unop) →ₗ[Γ(X, V.unop)] Γ(X, V.unop) := (a.val.app V).hom
  let Fb : Γ(X, V.unop) →ₗ[Γ(X, V.unop)] Γ(X, V.unop) := (b.val.app V).hom
  change Fb (Fa 1) = Fa (Fb 1)
  rw [hF Fb (Fa 1), hF Fa (Fb 1), mul_comm]

/-- The actual derived pullback/direct-image adjunction unit for the projective line is
invertible at every perfect complex. -/
theorem projectiveLineDerivedUnit_isIso (X : Scheme.{u}) (K : DerivedCategory X.Modules)
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect (X := X.toRingedSpace) K) :
    IsIso ((derivedAdjunction (projectiveSpaceOver 1 X ↘ X).toLRSHom.toShHom).unit.app K) := by
  let P := projectiveSpaceOver 1 X
  let f := P ↘ X
  let φ := f.toLRSHom.toShHom
  let adj := derivedAdjunction φ
  let R := derivedPushforward φ
  let v := Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso φ
  apply unit_isIso_of_structure_unit _ _ hK
  obtain ⟨w₀⟩ :=
    Stacks.Duality.ProjectiveSpace.nonempty_derivedPushforward_twistOver_zero_iso 0 X
  let w : R.obj (U P.toRingedSpace) ≅ U X.toRingedSpace :=
    R.mapIso ((DerivedCategory.singleFunctor P.Modules 0).mapIso
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit 1 X).symm) ≪≫ w₀
  let η := adj.unit.app (U X.toRingedSpace)
  let a := adj.homEquiv _ _ v.hom
  have ha : a = η ≫ R.map v.hom := adj.homEquiv_unit _ _ _
  let t := (adj.homEquiv _ _).symm w.inv
  let b := v.inv ≫ t
  have hb : a ≫ R.map b = w.inv := by
    have hc : v.hom ≫ b = t := by simp [b]
    rw [ha, Category.assoc, ← R.map_comp, hc, ← Adjunction.homEquiv_unit]
    exact (adj.homEquiv _ _).apply_symm_apply w.inv
  have hab : (a ≫ w.hom) ≫ (w.inv ≫ R.map b ≫ w.hom) = 𝟙 _ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc a, hb, Iso.inv_hom_id]
  let S := DerivedCategory.singleFunctor X.Modules 0
  have hcomm (r s : U X.toRingedSpace ⟶ U X.toRingedSpace) : r ≫ s = s ≫ r := by
    obtain ⟨r', rfl⟩ := S.map_surjective r
    obtain ⟨s', rfl⟩ := S.map_surjective s
    exact (S.map_comp r' s').symm.trans
      ((congrArg S.map (structureSheaf_hom_comm X r' s')).trans (S.map_comp s' r'))
  let : IsIso (a ≫ w.hom) := ⟨_, hab, (hcomm _ _).trans hab⟩
  let : IsIso a := IsIso.of_isIso_comp_right a w.hom
  let : IsIso (R.map v.hom) := (R.mapIso v).isIso_hom
  let : IsIso (η ≫ R.map v.hom) := ha ▸ (inferInstance : IsIso a)
  exact IsIso.of_isIso_comp_right η (R.map v.hom)

local instance projectiveLinePullbackPreservesHomology (S : Scheme.{u}) :
    (modulePullback (projectiveSpaceOver 1 S ↘ S).toLRSHom.toShHom).PreservesHomology :=
  RingedSpaceModuleAdjunction.preservesHomology_modulePullback_of_isFlat _
    (fun x => Flat.stalkMap (projectiveSpaceOver 1 S ↘ S) x)

/-- The canonical bounded-below adjunction unit for the projective-line projection is an
isomorphism at every perfect object. The bounded-below and unbounded units are compared
through the same ordinary degreewise adjunction unit. -/
@[colib_tag "COL-1290", stacks 079W "unit on projective-line perfect coefficients",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativePerfectGeneration.lean:43"
    "generalization" "The canonical adjunction unit is an isomorphism, over any scheme."]
theorem isIso_projectiveLineDerivedUnitPlus (S : Scheme.{u})
    (K : DerivedCategory.Plus S.Modules)
    (hK : RingedSpace.IsPerfect (X := S.toRingedSpace) K.obj) :
    let f := projectiveSpaceOver 1 S ↘ S
    let φ := f.toLRSHom.toShHom
    IsIso ((modulePullbackPushforwardAdjunction φ).rightDerivedFunctorPlus.unit.app K) := by
  let X := projectiveSpaceOver 1 S
  let f := X ↘ S
  let φ := f.toLRSHom.toShHom
  let L := modulePullback φ
  let R := modulePushforward φ
  let adj := modulePullbackPushforwardAdjunction φ
  have hf : AlgebraicGeometry.IsFlat φ := fun x => Flat.stalkMap f x
  let : L.PreservesHomology := projectiveLinePullbackPreservesHomology S
  have hL := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let J := (DerivedCategory.Plus.Qh (C := S.Modules)).objPreimage K
  let J' := L.mapHomotopyCategoryPlus.obj J
  let K' := DerivedCategory.Plus.Qh.obj J
  let e : K' ≅ K := DerivedCategory.Plus.Qh.objObjPreimageIso K
  suffices IsIso (adj.rightDerivedFunctorPlus.unit.app K') from
    (NatTrans.isIso_app_iff_of_iso _ e).mp this
  have hK' : RingedSpace.IsPerfect (X := S.toRingedSpace) K'.obj :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := S.toRingedSpace) (DerivedCategory.Plus.ι.mapIso e).symm hK
  have hu := projectiveLineDerivedUnit_isIso S K'.obj hK'
  have hv := Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackComparison_app_of_isFlat
    φ hf J.obj
  have h := derivedAdjunction_unit_fac φ J.obj
  have hcomp : IsIso (DerivedCategory.Qh.map
        ((homotopyPullbackPushforwardAdjunction φ).unit.app J.obj) ≫
      (derivedPushforwardUnit φ).app J'.obj) := by
    have h' : (derivedAdjunction φ).unit.app (DerivedCategory.Qh.obj J.obj) ≫
          (derivedPushforward φ).map ((derivedPullbackComparison φ).app J.obj) =
        DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction φ).unit.app J.obj) ≫
          (derivedPushforwardUnit φ).app J'.obj := h
    exact h' ▸ IsIso.comp_isIso' hu
      ((derivedPushforward φ).mapIso (asIso ((derivedPullbackComparison φ).app J.obj))).isIso_hom
  let eR := (Stacks.DerivedFunctor.rightDerivedFunctorPlusCompιIso R).hom.app
    (DerivedCategory.Plus.Qh.obj J')
  have hc := Stacks.DerivedFunctor.rightDerivedFunctorPlusCompιIso_hom_app R J'
  have hc' : DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlusUnith.app J') ≫ eR =
      (derivedPushforwardUnit φ).app J'.obj := hc
  have he : DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app J)) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction φ).unit.app J.obj) := by
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι S.Modules).map
        (adj.mapHomotopyCategoryPlus.unit.app J)) = _
    rfl
  have h₁ : IsIso (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app J) ≫
      R.rightDerivedFunctorPlusUnith.app J') := by
    have h₂ : IsIso (DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app J) ≫
            R.rightDerivedFunctorPlusUnith.app J') ≫ eR) := by
      rw [Functor.map_comp, Category.assoc, hc', he]
      exact hcomp
    have h₃ := IsIso.of_isIso_comp_right
      (DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app J) ≫
          R.rightDerivedFunctorPlusUnith.app J')) eR
    let := h₃
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  rw [CategoryTheory.Adjunction.rightDerivedFunctorPlus_unit_app_Qh adj J, ← Category.assoc]
  have hunit : IsIso (L.rightDerivedFunctorPlusUnith.app J) :=
    ((asIso L.rightDerivedFunctorPlusUnith).app J).isIso_hom
  exact IsIso.comp_isIso' h₁
    (R.rightDerivedFunctorPlus.mapIso (asIso (L.rightDerivedFunctorPlusUnith.app J))).isIso_hom

end AlgebraicGeometry.projectiveSpaceOver
