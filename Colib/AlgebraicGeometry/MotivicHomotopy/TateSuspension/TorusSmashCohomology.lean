/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.CoordinateReduced
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.UnderlyingTorusKernel
public import Colib.CategoryTheory.Sites.Simplicial.ParameterSmashDerived
import Colib.CategoryTheory.Sites.Simplicial.ReducedPresheafCochainsSheafification
import Colib.CategoryTheory.Limits.PointedSmashFunctor
import Mathlib.CategoryTheory.Sites.LeftExact
import Colib.Algebra.Homology.DerivedCategory.KInjectiveHomNaturality

/-!
# Cohomology of the smash with the actual pointed torus

The reduced derived chains of the original torus smash compute derived
Hom into the original transfer contraction after forgetting transfers.
The coefficient comparison is induced by the unit of ordinary derived
presheaves on K-injective complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PointedSimplicialPresheaf AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers PointedSimplicialPresheaf.ParameterCoproduct
open scoped Simplicial

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "G" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "A" => LargeAb k
local notation "c" => ComplexShape.up ℤ

private theorem liftedPointedTorus_hom_eq :
    (liftedPointedTorus k).hom = liftedParameterPoint.{u + 1} (C := Cₖ) G (torusUnitPoint k) := by
  apply NatTrans.ext
  funext U
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

private abbrev torusParameterPointed : PointedSimplicialPresheaf.{u + 1} Cₖ :=
  Under.mk (show (⊤_ (Cₖᵒᵖ ⥤ SSet.{u + 1})) ⟶ liftedRepresentableInterval.{u + 1} G from
    liftedParameterPoint.{u + 1} (C := Cₖ) G (torusUnitPoint k))

private def liftedPointedTorusParameterIso :
    liftedPointedTorus k ≅ torusParameterPointed k where
  hom := Under.homMk (𝟙 _) (by
    rw [Category.comp_id]
    exact liftedPointedTorus_hom_eq k)
  inv := Under.homMk (𝟙 _) (by
    rw [Category.comp_id]
    exact (liftedPointedTorus_hom_eq k).symm)
  hom_inv_id := by apply Under.UnderMorphism.ext; exact Category.id_comp _
  inv_hom_id := by apply Under.UnderMorphism.ext; exact Category.id_comp _

variable [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private abbrev ordinaryReducedDerivedChains :
    PointedSimplicialPresheaf.{u + 1} Cₖ ⥤ DerivedCategory (Sheaf Jₖ A) :=
  reducedDerivedChains.{w₃, u + 1} Cₖ Jₖ

private abbrev ordinaryReducedPresheafCochains :
    PointedSimplicialPresheaf.{u + 1} Cₖ ⥤ CochainComplex (Cₖᵒᵖ ⥤ A) ℤ :=
  reducedPresheafCochains.{u + 1} Cₖ

local notation "N" => ordinaryReducedDerivedChains k
local notation "M₀" => ordinaryReducedPresheafCochains k

private def torusSmashParameterIso (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    Under.smash X (liftedPointedTorus k) ≅ Under.smash X (torusParameterPointed k) :=
  (Under.smashRightBifunctor.mapIso (liftedPointedTorusParameterIso k)).app X

private abbrev ordinaryCochainModel (L : DerivedCategory (Sheaf Jₖ A)) :
    CochainComplex (Sheaf Jₖ A) ℤ :=
  (Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf Jₖ A)).obj
    (DerivedCategory.Q.objPreimage L)

private def ordinaryCochainModelIso (L : DerivedCategory (Sheaf Jₖ A)) :
    DerivedCategory.Q.obj (ordinaryCochainModel k L) ≅ L := by
  let K := DerivedCategory.Q.objPreimage L
  let a := (Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf Jₖ A)).app K
  let : QuasiIso a := inferInstanceAs
    (QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf Jₖ A)).app K))
  exact (asIso (DerivedCategory.Q.map a)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L

private def ordinaryReducedPresheafHomEquiv
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (L : DerivedCategory (Sheaf Jₖ A)) :
    ((N).obj X ⟶ L) ≃
      (DerivedCategory.Q.obj ((M₀).obj X) ⟶
        (ordinaryPresheafDerivedFunctor k).obj L) := by
  let U := sheafToPresheaf Jₖ A
  let F := presheafToSheaf Jₖ A
  let R := ordinaryPresheafDerivedFunctor k
  let K := (M₀).obj X
  let I := ordinaryCochainModel k L
  let hI : I.IsKInjective := inferInstanceAs ((ordinaryCochainModel k L).IsKInjective)
  let : I.IsKInjective := hI
  let e := ordinaryCochainModelIso k L
  let hU : IsIso ((ordinaryPresheafDerivedUnit k).app I) := isIso_app_of_isKInjective
    DerivedCategory.Q R (ordinaryPresheafDerivedUnit k)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
  let d := @asIso _ _ _ _ ((ordinaryPresheafDerivedUnit k).app I) hU ≪≫ R.mapIso e
  let : CochainComplex.IsKInjective (((U).mapHomologicalComplex c).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact U F
      (sheafificationAdjunction Jₖ A) I
  let b₀ : reducedCochains.{u + 1} Cₖ Jₖ ≅ (M₀) ⋙ F.mapHomologicalComplex c :=
    reducedCochainsSheafificationIso.{u + 1, u, u + 1} Cₖ Jₖ
  let b := DerivedCategory.Q.mapIso (b₀.app X)
  exact ((b.homCongr e.symm).trans
    ((sheafificationAdjunction Jₖ A).kInjectiveHomAddEquiv K I).symm.toEquiv).trans
    ((Iso.refl _).homCongr d)

omit [HasDerivedCategory (LargePresheaves k)] [HasDerivedCategory (LargeSheaves k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem ordinaryReducedPresheafHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    (L : DerivedCategory (Sheaf Jₖ A)) (g : (N).obj Y ⟶ L) :
    ordinaryReducedPresheafHomEquiv k X L ((N).map f ≫ g) =
      DerivedCategory.Q.map ((M₀).map f) ≫ ordinaryReducedPresheafHomEquiv k Y L g := by
  let I := ordinaryCochainModel k L
  let : I.IsKInjective := inferInstanceAs ((ordinaryCochainModel k L).IsKInjective)
  let U := sheafToPresheaf Jₖ A
  let F := presheafToSheaf Jₖ A
  let a := sheafificationAdjunction Jₖ A
  let : CochainComplex.IsKInjective ((U.mapHomologicalComplex c).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact U F a I
  let e := ordinaryCochainModelIso k L
  let R := ordinaryPresheafDerivedFunctor k
  let hU : IsIso ((ordinaryPresheafDerivedUnit k).app I) := isIso_app_of_isKInjective
    DerivedCategory.Q R (ordinaryPresheafDerivedUnit k)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I inferInstance
  let d := @asIso _ _ _ _ ((ordinaryPresheafDerivedUnit k).app I) hU ≪≫ R.mapIso e
  let b : reducedCochains.{u + 1} Cₖ Jₖ ≅ (M₀) ⋙ F.mapHomologicalComplex c :=
    reducedCochainsSheafificationIso.{u + 1, u, u + 1} Cₖ Jₖ
  let bX := DerivedCategory.Q.mapIso (b.app X)
  let bY := DerivedCategory.Q.mapIso (b.app Y)
  let x := (M₀).map f
  let z := DerivedCategory.Q.map ((F.mapHomologicalComplex c).map x)
  let t := bY.inv ≫ g ≫ e.inv
  have hb : bX.inv ≫ (N).map f = z ≫ bY.inv := by
    change DerivedCategory.Q.map (b.inv.app X) ≫
        DerivedCategory.Q.map ((reducedCochains.{u + 1} Cₖ Jₖ).map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex c).map x) ≫
        DerivedCategory.Q.map (b.inv.app Y)
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact DerivedCategory.Q.congr_map (b.inv.naturality f).symm
  have hp : bX.inv ≫ ((N).map f ≫ g) ≫ e.inv = z ≫ t := by
    calc
      _ = (bX.inv ≫ (N).map f) ≫ g ≫ e.inv := by simp only [Category.assoc]
      _ = (z ≫ bY.inv) ≫ g ≫ e.inv := congrArg (fun h => h ≫ g ≫ e.inv) hb
      _ = _ := Category.assoc _ _ _
  let P (Z : PointedSimplicialPresheaf.{u + 1} Cₖ) := a.kInjectiveHomAddEquiv ((M₀).obj Z) I
  have h : (P X).symm (z ≫ t) =
      DerivedCategory.Q.map x ≫ (P Y).symm t :=
    a.kInjectiveHomAddEquiv_symm_precomp I x t
  unfold ordinaryReducedPresheafHomEquiv
  change (𝟙 _ ≫ (P X).symm (bX.inv ≫ ((N).map f ≫ g) ≫ e.inv) ≫ d.hom) =
    DerivedCategory.Q.map x ≫ (𝟙 _ ≫ (P Y).symm t ≫ d.hom)
  rw [Category.id_comp, Category.id_comp, hp, h, Category.assoc]

/-- The actual torus smash computes derived Hom into the reduced
transfer torus sections after forgetting transfers. -/
@[no_expose]
def torusSmashDerivedHomEquiv
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (K : DerivedCategory (LargeSheaves k)) :
    let F := (toSheaf k).mapDerivedCategory
    let R := reducedTorusSectionsDerivedFunctor k
    let N₀ := reducedDerivedChains.{w₃, u + 1} Cₖ Jₖ
    (N₀.obj (Under.smash X (liftedPointedTorus k)) ⟶ F.obj K) ≃
      (N₀.obj X ⟶ F.obj (R.obj K)) := by
  intro F R N₀
  let L := F.obj K
  let U := sheafToPresheaf Jₖ A
  let D := ordinaryPresheafDerivedFunctor k
  let P := reindex G A
  let K₀ := DerivedCategory.Q.obj ((M₀).obj X)
  let Y := torusParameterPointed k
  let I := ordinaryCochainModel k L
  let hI : I.IsKInjective := inferInstanceAs ((ordinaryCochainModel k L).IsKInjective)
  let : I.IsKInjective := hI
  let e := ordinaryCochainModelIso k L
  let hU : IsIso ((ordinaryPresheafDerivedUnit k).app I) := isIso_app_of_isKInjective
    DerivedCategory.Q D (ordinaryPresheafDerivedUnit k)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
  let d := @asIso _ _ _ _ ((ordinaryPresheafDerivedUnit k).app I) hU ≪≫ D.mapIso e
  let M := ((U).mapHomologicalComplex c).obj I
  let b := (P.mapDerivedCategoryFactors.app M).symm ≪≫ P.mapDerivedCategory.mapIso d
  let j := DerivedCategory.Q.map
    ((homologicalPointRestriction G A (torusUnitPoint k) c).app M)
  let ρ := ordinaryTorusDerivedUnitRestriction k
  have h : b.hom ≫ ρ.app (D.obj L) = j ≫ d.hom := by
    change (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map d.hom) ≫
      ρ.app (D.obj L) = _
    rw [Category.assoc, ρ.naturality d.hom, ← Category.assoc]
    exact congrArg (· ≫ d.hom) (ordinaryTorusDerivedUnitRestriction_app_Q_obj k M)
  let hB := (Iso.refl K₀).homCongr b
  have hB₀ (f : K₀ ⟶ DerivedCategory.Q.obj ((P.mapHomologicalComplex c).obj M)) :
      f ≫ j = 0 ↔ hB f ≫ ρ.app (D.obj L) = 0 := by
    change f ≫ j = 0 ↔ (𝟙 K₀ ≫ f ≫ b.hom) ≫ ρ.app (D.obj L) = 0
    rw [Category.id_comp, Category.assoc, h, ← Category.assoc]
    exact ⟨fun h' => by rw [h', zero_comp], fun h' =>
      (cancel_mono d.hom).1 (h'.trans zero_comp.symm)⟩
  let e₀ := (N).mapIso (torusSmashParameterIso k X)
  let hB₁ := hB.subtypeEquiv
    (p := fun f => f ≫ j = 0) (q := fun f => f ≫ ρ.app (D.obj L) = 0) hB₀
  exact (e₀.homCongr e.symm).trans ((parameterSmashDerivedHomEquiv.{w₃, w₄, u + 1} Jₖ G
    (torusUnitPoint k) X I).trans (hB₁.trans
      ((ordinaryPresheafReducedTorusHomEquiv k K₀ K).symm.trans
        (ordinaryReducedPresheafHomEquiv k X (F.obj (R.obj K))).symm)))

/-- The original torus-smash comparison retains the original pointed maps. -/
theorem torusSmashDerivedHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    (K : DerivedCategory (LargeSheaves k)) :
    let L := (toSheaf k).mapDerivedCategory.obj K
    let N₀ := reducedDerivedChains.{w₃, u + 1} Cₖ Jₖ
    ∀ g : N₀.obj (Under.smash Y (liftedPointedTorus k)) ⟶ L,
      torusSmashDerivedHomEquiv k X K
        (N₀.map (Under.smashMap f (𝟙 (liftedPointedTorus k))) ≫ g) =
      N₀.map f ≫ torusSmashDerivedHomEquiv k Y K g := by
  intro L N₀ g
  let F := (toSheaf k).mapDerivedCategory
  let R := reducedTorusSectionsDerivedFunctor k
  let K' := F.obj (R.obj K)
  let D := ordinaryPresheafDerivedFunctor k
  let U := sheafToPresheaf Jₖ A
  let P := reindex G A
  let I := ordinaryCochainModel k L
  let hI : I.IsKInjective := inferInstanceAs ((ordinaryCochainModel k L).IsKInjective)
  let : I.IsKInjective := hI
  let e := ordinaryCochainModelIso k L
  let hU : IsIso ((ordinaryPresheafDerivedUnit k).app I) := isIso_app_of_isKInjective
    DerivedCategory.Q D (ordinaryPresheafDerivedUnit k)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
  let d := @asIso _ _ _ _ ((ordinaryPresheafDerivedUnit k).app I) hU ≪≫ D.mapIso e
  let M := ((U).mapHomologicalComplex c).obj I
  let b := (P.mapDerivedCategoryFactors.app M).symm ≪≫ P.mapDerivedCategory.mapIso d
  let j := liftedPointedTorusParameterIso k
  let t (Z : PointedSimplicialPresheaf.{u + 1} Cₖ) :=
    (N).mapIso (torusSmashParameterIso k Z)
  let a₀ := (N).map (Under.smashMap f (𝟙 (liftedPointedTorus k)))
  let a₁ := (N).map (Under.smashMap f (𝟙 (torusParameterPointed k)))
  let x := DerivedCategory.Q.map ((M₀).map f)
  let h := (t Y).inv ≫ g ≫ e.inv
  have hT : (t X).inv ≫ a₀ = a₁ ≫ (t Y).inv := by
    change (N).map (torusSmashParameterIso k X).inv ≫ a₀ =
      a₁ ≫ (N).map (torusSmashParameterIso k Y).inv
    dsimp only [a₀, a₁]
    rw [← (N).map_comp, ← (N).map_comp]
    exact (N).congr_map (((Under.smashRightBifunctor.mapIso j).inv.naturality f).symm)
  have hP : (t X).inv ≫ (a₀ ≫ g) ≫ e.inv = a₁ ≫ h := by
    calc
      _ = ((t X).inv ≫ a₀) ≫ g ≫ e.inv := by simp only [Category.assoc]
      _ = (a₁ ≫ (t Y).inv) ≫ g ≫ e.inv := congrArg (fun u => u ≫ g ≫ e.inv) hT
      _ = _ := Category.assoc _ _ _
  let E (Z : PointedSimplicialPresheaf.{u + 1} Cₖ) :=
    parameterSmashDerivedHomEquiv.{w₃, w₄, u + 1} Jₖ G (torusUnitPoint k) Z I
  have hE : (E X (a₁ ≫ h)).val = x ≫ (E Y h).val :=
    parameterSmashDerivedHomEquiv_precomp.{w₃, w₄, u + 1} Jₖ G (torusUnitPoint k) f I h
  let H (Z : PointedSimplicialPresheaf.{u + 1} Cₖ) := ordinaryReducedPresheafHomEquiv k Z K'
  apply (H X).injective
  have hg₁ : (H X) ((N₀.map f) ≫ torusSmashDerivedHomEquiv k Y K g) =
      x ≫ (H Y) (torusSmashDerivedHomEquiv k Y K g) :=
    ordinaryReducedPresheafHomEquiv_precomp k f K' (torusSmashDerivedHomEquiv k Y K g)
  rw [hg₁]
  let j₀ := (torusSectionsDerivedOrdinaryPresheafIso k).inv.app K
  let p₀ := (F ⋙ D).map ((reducedTorusSectionsDerivedProjection k).app K)
  have he (Z : PointedSimplicialPresheaf.{u + 1} Cₖ)
      (v : (N).obj (Under.smash Z (liftedPointedTorus k)) ⟶ L) :
      H Z (torusSmashDerivedHomEquiv k Z K v) =
        ((E Z ((t Z).inv ≫ v ≫ e.inv)).val ≫ b.hom) ≫ j₀ ≫ p₀ := by
    unfold torusSmashDerivedHomEquiv
    simp only [Equiv.trans_apply, Iso.homCongr_apply]
    change H Z ((H Z).symm _) = _
    rw [(H Z).apply_symm_apply]
    refine (ordinaryPresheafReducedTorusHomEquiv_symm_apply k
      (DerivedCategory.Q.obj ((M₀).obj Z)) K _).trans ?_
    change ((𝟙 _ ≫ (E Z ((t Z).inv ≫ v ≫ e.inv)).val ≫ b.hom) ≫ j₀ ≫ p₀) = _
    rw [Category.id_comp]
  have hX := he X (a₀ ≫ g)
  have hY := he Y g
  change H X (torusSmashDerivedHomEquiv k X K (a₀ ≫ g)) =
    x ≫ H Y (torusSmashDerivedHomEquiv k Y K g)
  rw [hX, hY, hP, hE]
  change ((x ≫ (E Y h).val) ≫ b.hom) ≫ j₀ ≫ p₀ =
    x ≫ ((E Y h).val ≫ b.hom) ≫ j₀ ≫ p₀
  simp only [Category.assoc]

end AlgebraicGeometry.MotivicHomotopy
