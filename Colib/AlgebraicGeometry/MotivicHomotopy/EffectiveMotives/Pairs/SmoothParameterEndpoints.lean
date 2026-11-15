/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.ProjectiveModel
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardParameterMap
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-! # Smooth parameter comparisons on the original projective endpoints -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance smoothParameterEndpointsAbelian : Abelian NST := SheafWithTransfers.abelian k
set_option quotPrecheck false in
local notation "R" => representableLarge k
set_option quotPrecheck false in
local notation "a" => nisnevichSheafify k
set_option quotPrecheck false in
local notation "γ" => Cor.graphFunctor k
local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "s" => CochainComplex.singleFunctor NST 0

variable {T : SmoothSite (Spec (CommRingCat.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)

set_option quotPrecheck false in
local notation "H" => coendPushforward F
set_option quotPrecheck false in
local notation "J" => (H ⋙ a)
set_option quotPrecheck false in
local notation "G" => parameterProduct T

/-- On the original representables, the coend and the graph comparison
give the actual represented product in degree zero. -/
def smoothParameterCochainEndpointIso (X : Sm) :
    ((J).mapHomologicalComplex c).obj ((projectiveSmoothSingle k).obj X) ≅
      (s).obj ((smoothTransferRepresentable k).obj ((G).obj X)) :=
  (HomologicalComplex.singleMapHomologicalComplex J c (0 : ℤ)).app ((R).obj (Cor.mk X)) ≪≫
    (s).mapIso ((a).mapIso (coendPushforwardRepresentableIso F (Cor.mk X) ≪≫
      (R).mapIso (e.app X)))

set_option maxHeartbeats 650000 in
-- Keep the two represented endpoints typed before applying the comparison.
/-- The endpoint comparison sends original graphs to their actual products. -/
theorem smoothParameterCochainEndpointIso_naturality {X Y : Sm} (f : X ⟶ Y) :
    ((J).mapHomologicalComplex c).map ((projectiveSmoothSingle k).map f) ≫
        (smoothParameterCochainEndpointIso e Y).hom =
      (smoothParameterCochainEndpointIso e X).hom ≫
        (s).map ((smoothTransferRepresentable k).map ((G).map f)) := by
  let x := (γ).map f
  let x' := (γ).map ((G).map f)
  let m := (R).map x
  let m' := (R).map x'
  let d := HomologicalComplex.singleMapHomologicalComplex J c (0 : ℤ)
  let t (X : Sm) := (coendPushforwardRepresentableIso F (Cor.mk X)).hom
  let i (X : Sm) := (R).map (e.hom.app X)
  have ht : (H).map m ≫ t Y = t X ≫ (R).map (F.map x) :=
    coendPushforwardRepresentableIso_naturality F x
  have hu : F.map x ≫ e.hom.app Y = e.hom.app X ≫ x' :=
    e.hom.naturality f
  have hi : (R).map (F.map x) ≫ i Y = i X ≫ m' :=
    ((R).map_comp _ _).symm.trans (((R).congr_map hu).trans ((R).map_comp _ _))
  have h : (H).map m ≫ (t Y ≫ i Y) = (t X ≫ i X) ≫ m' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ i Y) ht).trans
      ((Category.assoc _ _ _).trans ((congrArg (t X ≫ ·) hi).trans (Category.assoc _ _ _).symm)))
  let f₀ := ((J).mapHomologicalComplex c).map ((CochainComplex.singleFunctor PST 0).map m)
  let g₀ := (s).map ((J).map m)
  let d₀ := d.hom.app ((R).obj (Cor.mk X))
  let d₁ := d.hom.app ((R).obj (Cor.mk Y))
  let h₀ := (s).map ((a).map (t X ≫ i X))
  let h₁ := (s).map ((a).map (t Y ≫ i Y))
  let g₁ := (s).map ((a).map m')
  have hn : f₀ ≫ d₁ = d₀ ≫ g₀ := d.hom.naturality m
  have hm : g₀ ≫ h₁ = h₀ ≫ g₁ := by
    have hh : (J).map m ≫ (a).map (t Y ≫ i Y) =
        (a).map (t X ≫ i X) ≫ (a).map m' :=
      ((a).map_comp _ _).symm.trans (((a).congr_map h).trans ((a).map_comp _ _))
    exact ((s).map_comp _ _).symm.trans (((s).congr_map hh).trans ((s).map_comp _ _))
  have hₓ : (smoothParameterCochainEndpointIso e X).hom = d₀ ≫ h₀ := rfl
  have hᵧ : (smoothParameterCochainEndpointIso e Y).hom = d₁ ≫ h₁ := rfl
  change f₀ ≫ _ = _ ≫ g₁
  exact (congrArg (f₀ ≫ ·) hᵧ).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ h₁) hn).trans ((Category.assoc _ _ _).trans
      ((congrArg (d₀ ≫ ·) hm).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g₁) hₓ.symm))))))

section ParameterMap

variable {T' : SmoothSite (Spec (CommRingCat.of k))} {F' : Cor k ⥤ Cor k} [F'.Additive]
  (e' : Cor.graphFunctor k ⋙ F' ≅ parameterProduct T' ⋙ Cor.graphFunctor k)
  (g : T ⟶ T') (η : F ⟶ F')
  (hη : ∀ X : SmoothSite (Spec (CommRingCat.of k)), η.app (Cor.mk X) ≫ e'.hom.app X =
    e.hom.app X ≫ (Cor.graphFunctor k).map ((parameterMap g).app X))

set_option maxHeartbeats 950000 in
-- Seat the two degree-zero comparisons before applying the parameter transformation.
include hη in
/-- The endpoint comparison sends a change of parameter to the original product map. -/
theorem smoothParameterCochainEndpointIso_parameter (X : Sm) :
    (((Functor.whiskerRight (coendPushforwardParameterMap η) a).mapHomologicalComplex c).app
      ((projectiveSmoothSingle k).obj X)) ≫ (smoothParameterCochainEndpointIso e' X).hom =
    (smoothParameterCochainEndpointIso e X).hom ≫
      (s).map ((smoothTransferRepresentable k).map ((parameterMap g).app X)) := by
  let t := coendPushforwardParameterMap η
  let J' := coendPushforward F' ⋙ a
  let τ := Functor.whiskerRight t a
  let p := (R).obj (Cor.mk X)
  let b := (coendPushforwardRepresentableIso F (Cor.mk X)).hom ≫ (R).map (e.hom.app X)
  let b' := (coendPushforwardRepresentableIso F' (Cor.mk X)).hom ≫ (R).map (e'.hom.app X)
  let i := (HomologicalComplex.singleMapHomologicalComplex J c (0 : ℤ)).app p
  let i' := (HomologicalComplex.singleMapHomologicalComplex J' c (0 : ℤ)).app p
  let h := (R).map ((γ).map ((parameterMap g).app X))
  have he : t.app p ≫ b' = b ≫ h := by
    dsimp only [b, b']
    rw [← Category.assoc, coendPushforwardRepresentableIso_parameterMap, Category.assoc,
      ← (R).map_comp, hη X, (R).map_comp, Category.assoc]
  let q := (τ.mapHomologicalComplex c).app ((CochainComplex.singleFunctor PST 0).obj p)
  have hq : q ≫ i'.hom = i.hom ≫ (s).map ((a).map (t.app p)) := by
    have hcomp := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj_assoc
      τ c (0 : ℤ) p i'.hom
    change q ≫ i'.hom = i.hom ≫ (s).map ((a).map (t.app p)) ≫ i'.inv ≫ i'.hom at hcomp
    exact hcomp.trans ((congrArg (i.hom ≫ (s).map ((a).map (t.app p)) ≫ ·) i'.inv_hom_id).trans
      ((Category.assoc _ _ _).symm.trans (Category.comp_id _)))
  have hcoeff : (a).map (t.app p) ≫ (a).map b' = (a).map b ≫ (a).map h :=
    ((a).map_comp _ _).symm.trans (((a).congr_map he).trans ((a).map_comp _ _))
  have hb : (s).map ((a).map (t.app p)) ≫ (s).map ((a).map b') =
      (s).map ((a).map b) ≫ (s).map ((a).map h) :=
    ((s).map_comp _ _).symm.trans (((s).congr_map hcoeff).trans ((s).map_comp _ _))
  change q ≫ (i'.hom ≫ (s).map ((a).map b')) =
    (i.hom ≫ (s).map ((a).map b)) ≫ (s).map ((a).map h)
  rw [← Category.assoc, hq, Category.assoc, hb, Category.assoc]

end ParameterMap

end AlgebraicGeometry.MotivicHomotopy
