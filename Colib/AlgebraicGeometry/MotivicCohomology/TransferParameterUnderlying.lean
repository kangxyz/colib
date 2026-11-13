/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterCochainUnderlying
public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterShiftMap

/-!
# Forgetting transfers on the signed parameter map

The degreewise ordinary comparison uses the same singular product
and the same sheafification unit. The comparison commutes with
extension by zero and the two signed shifts of the motivic parameter map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open Stacks.DerivedIndexing

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "F" => SheafWithTransfers.toSheaf k
local notation "A" => nisnevichSheafify k
local notation "B" => SheafWithTransfers.torusSectionsFunctor k
local notation "O" => torusParameterSheafFunctor k
local notation "c" => ComplexShape.down ℕ
local notation "d" => ComplexShape.up ℤ
local notation "e" => ComplexShape.embeddingUpIntLE 0
local notation "φ" => SheafWithTransfers.torusSectionsToSheafIso k

private theorem mapHomologicalComplex_comp_commShift
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (G : C ⥤ C) (U : C ⥤ D) (H : D ⥤ D) [G.Additive] [U.Additive] [H.Additive]
    (τ : G ⋙ U ⟶ U ⋙ H) :
    NatTrans.CommShift
      (show G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⟶
        U.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) from
          τ.mapHomologicalComplex (.up ℤ)) ℤ := by
  let G' := G.mapHomologicalComplex (.up ℤ)
  let U' := U.mapHomologicalComplex (.up ℤ)
  let H' := H.mapHomologicalComplex (.up ℤ)
  let a := Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ U)) (.up ℤ)
  let b := Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ H)) (.up ℤ)
  let h := τ.mapHomologicalComplex (.up ℤ)
  let : NatTrans.CommShift a.hom ℤ := inferInstanceAs
    (NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ U)) (.up ℤ)).hom ℤ)
  let : NatTrans.CommShift b.hom ℤ := inferInstanceAs
    (NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ H)) (.up ℤ)).hom ℤ)
  let : NatTrans.CommShift b.inv ℤ := inferInstance
  let : NatTrans.CommShift h ℤ := inferInstanceAs
    (NatTrans.CommShift (τ.mapHomologicalComplex (.up ℤ)) ℤ)
  have hcomp : (show G' ⋙ U' ⟶ U' ⋙ H' from h) = a.hom ≫ h ≫ b.inv := by
    apply NatTrans.ext
    funext K
    apply HomologicalComplex.hom_f_injective
    funext i
    let f := τ.app (K.X i)
    let X := U.obj (G.obj (K.X i))
    let Y := H.obj (U.obj (K.X i))
    change f = (𝟙 X) ≫ f ≫ 𝟙 Y
    exact ((Category.id_comp (f ≫ 𝟙 Y)).trans (Category.comp_id f)).symm
  let v : G' ⋙ U' ⟶ U' ⋙ H' := h
  change NatTrans.CommShift v ℤ
  have hv : v = a.hom ≫ h ≫ b.inv := hcomp
  exact hv.symm ▸ (inferInstance : NatTrans.CommShift (a.hom ≫ h ≫ b.inv) ℤ)

private theorem shiftTransport
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (T : C ⥤ C) (U : C ⥤ D) (H : D ⥤ D)
    [T.CommShift ℤ] [U.CommShift ℤ] [H.CommShift ℤ]
    (θ : T ⋙ U ⟶ U ⋙ H) [NatTrans.CommShift θ ℤ] (s : ℤ) (K : C) :
    let a := (T.commShiftIso s).app K
    let b := (U.commShiftIso s).app K
    let x := (U.commShiftIso s).app (T.obj K)
    let y := (H.commShiftIso s).app (U.obj K)
    U.map a.inv ≫ θ.app (K⟦s⟧) =
      x.hom ≫ (shiftFunctor D s).map (θ.app K) ≫ y.inv ≫ H.map b.inv := by
  intro a b x y
  let S := shiftFunctor D s
  let dR := ((U ⋙ H).commShiftIso s).app K
  let dL := ((T ⋙ U).commShiftIso s).app K
  have h := NatTrans.shift_app_comm θ s K
  change dL.hom ≫ S.map (θ.app K) = θ.app (K⟦s⟧) ≫ dR.hom at h
  have hR : dR.hom = H.map b.hom ≫ y.hom := Functor.commShiftIso_comp_hom_app U H s K
  have hL : dL.hom = U.map a.hom ≫ x.hom := Functor.commShiftIso_comp_hom_app T U s K
  have hUa : U.map a.inv ≫ U.map a.hom = 𝟙 (U.obj ((T ⋙ shiftFunctor C s).obj K)) :=
    (U.map_comp _ _).symm.trans ((U.congr_map a.inv_hom_id).trans (U.map_id _))
  have hHb : H.map b.inv ≫ H.map b.hom = 𝟙 (H.obj ((U ⋙ shiftFunctor D s).obj K)) :=
    (H.map_comp _ _).symm.trans ((H.congr_map b.inv_hom_id).trans (H.map_id _))
  apply (cancel_mono dR.hom).1
  calc
    _ = U.map a.inv ≫ (dL.hom ≫ S.map (θ.app K)) :=
      (Category.assoc _ _ _).trans (congrArg (U.map a.inv ≫ ·) h.symm)
    _ = x.hom ≫ S.map (θ.app K) := by
      rw [hL]
      simp only [Category.assoc, reassoc_of% hUa]
    _ = _ := by
      symm
      rw [hR]
      simp only [Category.assoc, reassoc_of% hHb, y.inv_hom_id]
      exact congrArg (x.hom ≫ ·) (Category.comp_id (S.map (θ.app K)))

private theorem shiftAdditionTransport
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (U : C ⥤ D) [U.CommShift ℤ] (s t : ℤ) (h : t + 1 = s) (K : C) :
    let x := (shiftFunctorAdd' C t 1 s h).hom.app K
    let δ := (shiftFunctorAdd' D t 1 s h).app (U.obj K)
    let a := (U.commShiftIso (1 : ℤ)).app (K⟦t⟧)
    let b := (U.commShiftIso t).app K
    (U.commShiftIso s).inv.app K ≫ U.map x =
      δ.hom ≫ (shiftFunctor D (1 : ℤ)).map b.inv ≫ a.inv := by
  intro x δ a b
  let p := (U.commShiftIso s).app K
  let S := shiftFunctor D (1 : ℤ)
  let i := S.mapIso b
  let j := a ≪≫ i ≪≫ δ.symm
  have hj : p.hom = U.map x ≫ j.hom := by
    have h' := NatTrans.congr_app (congrArg Iso.hom (U.commShiftIso_add' h)) K
    rw [Functor.CommShift.isoAdd'_hom_app] at h'
    exact h'
  have h' : p.inv ≫ U.map x = j.inv := by
    apply (cancel_mono j.hom).1
    exact (Category.assoc _ _ _).trans
      ((congrArg (p.inv ≫ ·) hj.symm).trans (p.inv_hom_id.trans j.inv_hom_id.symm))
  exact h'.trans (Category.assoc _ _ _)

private theorem shiftedTargetTransport
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (U : C ⥤ D) [U.CommShift ℤ] (s t : ℤ) (h : t + 1 = s) (K : C)
    {M : D} (r : U.obj K ≅ M) :
    let S := shiftFunctor D s
    let T := shiftFunctor D t
    let W := shiftFunctor D (1 : ℤ)
    let δ := (shiftFunctorAdd' D t 1 s h).hom
    let x := (shiftFunctorAdd' C t 1 s h).hom.app K
    let j := (U.commShiftIso s).inv.app K
    let b := (U.commShiftIso t).inv.app K
    j ≫ U.map x ≫ (U.commShiftIso (1 : ℤ)).hom.app (K⟦t⟧) =
      S.map r.hom ≫ δ.app M ≫ W.map (T.map r.inv ≫ b) := by
  intro S T W δ x j b
  let a := (U.commShiftIso (1 : ℤ)).app (K⟦t⟧)
  let u := T.map r.hom
  let v := T.map r.inv
  let z := δ.app (U.obj K)
  have h₁ : j ≫ U.map x = z ≫ W.map b ≫ a.inv :=
    shiftAdditionTransport U s t h K
  have hn : S.map r.hom ≫ δ.app M = z ≫ W.map u := δ.naturality r.hom
  have h₂ : W.map u ≫ W.map v = 𝟙 (W.obj (T.obj (U.obj K))) :=
    (W.mapIso (T.mapIso r)).hom_inv_id
  calc
    _ = (j ≫ U.map x) ≫ a.hom := (Category.assoc _ _ _).symm
    _ = (z ≫ W.map b ≫ a.inv) ≫ a.hom := congrArg (· ≫ a.hom) h₁
    _ = z ≫ W.map b := by
      simp only [Category.assoc, a.inv_hom_id]
      exact congrArg (z ≫ ·) (Category.comp_id (W.map b))
    _ = z ≫ (W.map u ≫ W.map v) ≫ W.map b :=
      (congrArg (z ≫ ·) (Category.id_comp _)).symm.trans
        (congrArg (fun m => z ≫ m ≫ W.map b) h₂).symm
    _ = (z ≫ W.map u) ≫ W.map (v ≫ b) := by
      rw [W.map_comp]
      simp only [Category.assoc]
    _ = _ := (congrArg (· ≫ W.map (v ≫ b)) hn.symm).trans (Category.assoc _ _ _)

private theorem shiftedComparison
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (T : C ⥤ C) (U : C ⥤ D) (H : D ⥤ D)
    [T.CommShift ℤ] [U.CommShift ℤ] [H.CommShift ℤ]
    (θ : T ⋙ U ⟶ U ⋙ H) [NatTrans.CommShift θ ℤ] (s : ℤ)
    {K L Z : C} {M N : D}
    (f : K ⟶ T.obj L) (g : M ⟶ H.obj N) (p : U.obj K ⟶ M) (r : U.obj L ⟶ N)
    (x : L⟦s⟧ ⟶ Z) (y : N⟦s⟧ ⟶ U.obj Z)
    (h : U.map f ≫ θ.app L ≫ H.map r = p ≫ g)
    (hx : (U.commShiftIso s).inv.app L ≫ U.map x = (shiftFunctor D s).map r ≫ y) :
    U.map ((shiftFunctor C s).map f ≫ (T.commShiftIso s).inv.app L ≫ T.map x) ≫
        θ.app Z =
      (U.commShiftIso s).hom.app K ≫ (shiftFunctor D s).map p ≫
        (shiftFunctor D s).map g ≫ (H.commShiftIso s).inv.app N ≫ H.map y := by
  let S := shiftFunctor D s
  let dK := (U.commShiftIso s).app K
  let dL := (U.commShiftIso s).app L
  let dT := (U.commShiftIso s).app (T.obj L)
  let hL := (H.commShiftIso s).app (U.obj L)
  let hN := (H.commShiftIso s).app N
  let x' := (T.commShiftIso s).inv.app L
  let f' := (shiftFunctor C s).map f
  have ht : U.map x' ≫ θ.app (L⟦s⟧) =
      dT.hom ≫ S.map (θ.app L) ≫ hL.inv ≫ H.map dL.inv :=
    shiftTransport T U H θ s L
  have hn : U.map (T.map x) ≫ θ.app Z = θ.app (L⟦s⟧) ≫ H.map (U.map x) :=
    θ.naturality x
  have hf : U.map f' ≫ dT.hom = dK.hom ≫ S.map (U.map f) :=
    (U.commShiftIso s).hom.naturality f
  have hr : hL.inv ≫ H.map (S.map r) = S.map (H.map r) ≫ hN.inv :=
    ((H.commShiftIso s).inv.naturality r).symm
  have hx' : dL.inv ≫ U.map x = S.map r ≫ y := hx
  change U.map (f' ≫ x' ≫ T.map x) ≫ θ.app Z =
    dK.hom ≫ S.map p ≫ S.map g ≫ hN.inv ≫ H.map y
  calc
    _ = U.map f' ≫ U.map x' ≫ (U.map (T.map x) ≫ θ.app Z) := by
      simp only [U.map_comp, Category.assoc]
    _ = U.map f' ≫ (U.map x' ≫ θ.app (L⟦s⟧)) ≫ H.map (U.map x) :=
      (congrArg (fun z => U.map f' ≫ U.map x' ≫ z) hn).trans
        (congrArg (U.map f' ≫ ·) (Category.assoc _ _ _).symm)
    _ = U.map f' ≫ (dT.hom ≫ S.map (θ.app L) ≫ hL.inv ≫ H.map dL.inv) ≫
        H.map (U.map x) := congrArg (fun z => U.map f' ≫ z ≫ H.map (U.map x)) ht
    _ = (U.map f' ≫ dT.hom) ≫ S.map (θ.app L) ≫ hL.inv ≫ H.map dL.inv ≫
        H.map (U.map x) := by simp only [Category.assoc]
    _ = (dK.hom ≫ S.map (U.map f)) ≫ S.map (θ.app L) ≫ hL.inv ≫
        H.map dL.inv ≫ H.map (U.map x) := congrArg
          (fun z => z ≫ S.map (θ.app L) ≫ hL.inv ≫ H.map dL.inv ≫ H.map (U.map x)) hf
    _ = dK.hom ≫ S.map (U.map f) ≫ S.map (θ.app L) ≫ hL.inv ≫ H.map dL.inv ≫
        H.map (U.map x) := Category.assoc _ _ _
    _ = dK.hom ≫ S.map (U.map f) ≫ S.map (θ.app L) ≫ hL.inv ≫ H.map (S.map r ≫ y) :=
      congrArg (fun z => dK.hom ≫ S.map (U.map f) ≫ S.map (θ.app L) ≫ hL.inv ≫ z)
        ((H.map_comp _ _).symm.trans (H.congr_map hx'))
    _ = dK.hom ≫ S.map (U.map f) ≫ S.map (θ.app L) ≫
        (hL.inv ≫ H.map (S.map r)) ≫ H.map y := by
      simp only [H.map_comp, Category.assoc]
    _ = dK.hom ≫ S.map (U.map f) ≫ S.map (θ.app L) ≫
        (S.map (H.map r) ≫ hN.inv) ≫ H.map y :=
      congrArg (fun z => dK.hom ≫ S.map (U.map f) ≫ S.map (θ.app L) ≫ z ≫ H.map y) hr
    _ = dK.hom ≫ S.map (U.map f ≫ θ.app L ≫ H.map r) ≫ hN.inv ≫ H.map y := by
      simp only [S.map_comp, Category.assoc]
    _ = dK.hom ≫ S.map (p ≫ g) ≫ hN.inv ≫ H.map y :=
      congrArg (fun z => dK.hom ≫ S.map z ≫ hN.inv ≫ H.map y) h
    _ = _ := by simp only [S.map_comp, Category.assoc]

private theorem ordinarySignedTargetTransport (q : ℕ) :
    let Q := reducedTorus k (q + 1)
    let K := singularSheafCochainComplex k Q 0
    let N := (AlgebraicSimplex.sheafifiedSingularChainsFunctor k Jₖ).obj ((toPresheaf k).obj Q)
    let C := CochainComplex (SheafWithTransfers.{u + 1} k) ℤ
    let C' := CochainComplex (Sheaf Jₖ AddCommGrpCat.{u + 1}) ℤ
    let D : C ⥤ C' := (F).mapHomologicalComplex d
    let s := -(q : ℤ)
    let t := -((q + 1 : ℕ) : ℤ)
    let hs : t + 1 = s := by dsimp [s, t]; omega
    let x := (shiftFunctorAdd' C t 1 s hs).hom.app K
    let y := (shiftFunctorAdd' C' t 1 s hs).hom.app (N.extend e)
    let a := (D.commShiftIso (1 : ℤ)).app (K⟦t⟧)
    let W := shiftFunctor C' (1 : ℤ)
    let r := ordinarySingularCochainIso k Q
    let y' := y ≫ W.map (motivicSheafComplexOrdinaryShiftIso k (q + 1)).inv
    (D.commShiftIso s).inv.app K ≫ D.map x =
      (shiftFunctor C' s).map r.hom ≫ (y' ≫ a.inv) := by
  intro _Q K _N C C' D s t hs x y a W r y'
  let V := shiftFunctor C' s
  let a' := (D.commShiftIso t).app K
  let d' := motivicSheafComplexOrdinaryShiftIso k (q + 1)
  have h₃ : d'.inv = (shiftFunctor C' t).map r.inv ≫ a'.inv :=
    motivicSheafComplexOrdinaryShiftIso_inv_eq k (q + 1)
  have h' := shiftedTargetTransport D s t hs K r
  have h'' : (D.commShiftIso s).inv.app K ≫ D.map x ≫ a.hom =
      V.map r.hom ≫ y' :=
    h'.trans (congrArg (fun f => V.map r.hom ≫ y ≫ W.map f) h₃.symm)
  have hi : (D.map x ≫ a.hom) ≫ a.inv = D.map x :=
    (Category.assoc _ _ _).trans
      ((congrArg (D.map x ≫ ·) a.hom_inv_id).trans (Category.comp_id _))
  calc
    _ = ((D.commShiftIso s).inv.app K ≫ D.map x ≫ a.hom) ≫ a.inv :=
      (congrArg ((D.commShiftIso s).inv.app K ≫ ·) hi).symm.trans
        (Category.assoc _ _ _).symm
    _ = (V.map r.hom ≫ y') ≫ a.inv := congrArg (· ≫ a.inv) h''
    _ = _ := Category.assoc _ _ _

private theorem identify_signed_map
    {C : Type*} [Category* C] (H : C ⥤ C)
    {K L M N Y Z Z' : C} (p : K ⟶ L) (p' : L ⟶ M) (p₀ : K ⟶ M)
    (g : M ⟶ N) (h : N ⟶ H.obj Y)
    (y : Y ⟶ Z') (a : Z ≅ Z')
    (hp : p₀ = p ≫ p')
    (f : K ⟶ H.obj Z)
    (hf : f = p ≫ p' ≫ g ≫ h ≫ H.map (y ≫ a.inv)) :
    f ≫ H.map a.hom = p₀ ≫ g ≫ h ≫ H.map y := by
  have hy : (y ≫ a.inv) ≫ a.hom = y :=
    (Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) a.inv_hom_id).trans (Category.comp_id _))
  have hY : H.map (y ≫ a.inv) ≫ H.map a.hom = H.map y :=
    (H.map_comp _ _).symm.trans (H.congr_map hy)
  calc
    _ = (p ≫ p' ≫ g ≫ h ≫ H.map (y ≫ a.inv)) ≫ H.map a.hom :=
      congrArg (· ≫ H.map a.hom) hf
    _ = p ≫ p' ≫ g ≫ h ≫ H.map y := by simp only [Category.assoc, hY]
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ g ≫ h ≫ H.map y) hp.symm)

set_option maxHeartbeats 600000 in
-- Compare the original cochain constructions across the two signed shifts.
/-- After forgetting transfers, the signed integral parameter map is
the original map used in the motivic bonding construction. -/
theorem motivicTransferParameterProduct_underlying (q : ℕ) :
    ((F).mapHomologicalComplex d).map (motivicTransferParameterProduct k q) ≫
      (NatIso.mapHomologicalComplex (φ) d).hom.app
        ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧) =
    motivicSheafParameterProduct k q := by
  let P := reducedTorus k q
  let Q := reducedTorus k (q + 1)
  let K := singularSheafCochainComplex k Q 0
  let N := (AlgebraicSimplex.sheafifiedSingularChainsFunctor k Jₖ).obj ((toPresheaf k).obj Q)
  let C := CochainComplex (SheafWithTransfers.{u + 1} k) ℤ
  let C' := CochainComplex (Sheaf Jₖ AddCommGrpCat.{u + 1}) ℤ
  let D : C ⥤ C' := (F).mapHomologicalComplex d
  let T : C ⥤ C := (B).mapHomologicalComplex d
  let H : C' ⥤ C' := (O).mapHomologicalComplex d
  let θ : T ⋙ D ⟶ D ⋙ H := NatTrans.mapHomologicalComplex (φ).hom d
  let s := -(q : ℤ)
  let t := -((q + 1 : ℕ) : ℤ)
  let f := (singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q) ≫
    SheafWithTransfers.singularSheafCochainTorusSectionsMap k Q
  let g := ((e).extendFunctor _).map (sheafifiedReducedTorusSingularParameterProduct k q) ≫
    (mapExtendIso (O) e N).hom
  let p := ordinarySingularCochainIso k P
  let r := ordinarySingularCochainIso k Q
  let V := shiftFunctor C' s
  let W := shiftFunctor C' (1 : ℤ)
  have hs : t + 1 = s := by dsimp [s, t]; omega
  let x := (shiftFunctorAdd' C t 1 s hs).hom.app K
  let y := (shiftFunctorAdd' C' t 1 s hs).hom.app (N.extend e)
  let dB := (T.commShiftIso s).inv.app K
  let dH := (H.commShiftIso s).inv.app (N.extend e)
  let U : SheafWithTransfers.{u + 1} k ⥤ Sheaf Jₖ AddCommGrpCat.{u + 1} := F
  let G : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := B
  let H₀ : Sheaf Jₖ AddCommGrpCat.{u + 1} ⥤ Sheaf Jₖ AddCommGrpCat.{u + 1} := O
  let : NatTrans.CommShift θ ℤ := mapHomologicalComplex_comp_commShift G U H₀ (φ).hom
  let a := (D.commShiftIso (1 : ℤ)).app (K⟦t⟧)
  have h₁ : D.map f ≫ θ.app K ≫ H.map r.hom = p.hom ≫ g :=
    ordinarySingularCochainProduct k q
  let d' := motivicSheafComplexOrdinaryShiftIso k (q + 1)
  let y' := y ≫ W.map d'.inv
  have h₄ : (D.commShiftIso s).inv.app K ≫ D.map x =
      V.map r.hom ≫ (y' ≫ a.inv) := ordinarySignedTargetTransport k q
  let dP := (D.commShiftIso s).hom.app (singularSheafCochainComplex k P 0)
  have hP : (motivicSheafComplexOrdinaryShiftIso k q).hom = dP ≫ V.map p.hom :=
    motivicSheafComplexOrdinaryShiftIso_hom_eq k q
  have hf₀ : motivicTransferParameterProduct k q = shiftTorusParameterMap k s t hs f :=
    motivicTransferParameterProduct_eq_shiftTorusParameterMap k q
  have hh := shiftedComparison T D H θ s f g p.hom r.hom x (y' ≫ a.inv) h₁ h₄
  let Z := (motivicComplex k (q + 1))⟦(1 : ℤ)⟧
  have hF : D.map (motivicTransferParameterProduct k q) ≫ θ.app Z =
      D.map ((shiftFunctor C s).map f ≫ dB ≫ T.map x) ≫ θ.app Z := by
    have hu : D.map (motivicTransferParameterProduct k q) ≫ θ.app Z =
        D.map (shiftTorusParameterMap k s t hs f) ≫ θ.app Z :=
      congrArg (fun z => D.map z ≫ θ.app Z) hf₀
    exact hu
  let p₀ := (motivicSheafComplexOrdinaryShiftIso k q).hom
  have hO : motivicSheafParameterProduct k q = p₀ ≫ V.map g ≫ dH ≫ H.map y' :=
    motivicSheafParameterProduct_eq k q
  have hC : D.map ((shiftFunctor C s).map f ≫ dB ≫ T.map x) ≫ θ.app Z =
      p₀ ≫ V.map g ≫ dH ≫ H.map y' :=
    (cancel_mono (H.map a.hom)).1
      (identify_signed_map H dP (V.map p.hom) p₀ (V.map g) dH y' a hP _ hh)
  exact hF.trans (hC.trans hO.symm)

end AlgebraicGeometry.PresheafWithTransfers
