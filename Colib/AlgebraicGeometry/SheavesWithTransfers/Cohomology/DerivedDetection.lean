/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksFrontier.Homology.Ext.CorepresentedHomotopyComparison
import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Detection by actual smooth transfer representables

In a K-injective model the shifted Hom groups out of the smooth
representables are the pointwise cohomology of the underlying signed
presheaf complex. Transfer sheafification recovers the cohomology
sheaves from those actual presheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite ZeroObject
open Stacks.Cohomology.Corepresented

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k] [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- If all shifted Hom groups from the actual smooth transfer
representables vanish, the derived object vanishes. -/
theorem isZero_of_subsingleton_hom_transferRepresentable
    (E : DerivedCategory (SheafWithTransfers.{u + 1} k))
    (h : ∀ (X : Cor k) (p : ℤ),
      Subsingleton ((DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj X) ⟶
        E⟦p⟧)) :
    IsZero E := by
  let K := DerivedCategory.Q.objPreimage E
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor _).obj K
  let ι := (Stacks.Injectives.kInjectiveResolutionInclusion _).app K
  let : I.IsKInjective := inferInstanceAs
    (((Stacks.Injectives.kInjectiveResolutionFunctor _).obj K).IsKInjective)
  let : QuasiIso ι := inferInstanceAs (QuasiIso
    ((Stacks.Injectives.kInjectiveResolutionInclusion _).app K))
  let e : DerivedCategory.Q.obj I ≅ E :=
    (asIso (DerivedCategory.Q.map ι)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let U : SheafWithTransfers.{u + 1} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    SheafWithTransfers.forget k ⋙ PresheafWithTransfers.forget
  let J := ((U.mapHomologicalComplex (.up ℤ)).obj I)
  have hJ (p : ℤ) : IsZero (J.homology p) := (Functor.isZero_iff _).2 (by
    intro V
    let X := V.unop
    let G := U ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj V
    let R := (transferRepresentable k).obj X
    let c : preadditiveCoyoneda.obj (op R) ≅ G :=
      NatIso.ofComponents (fun F => (transferSectionsEquiv k X F).toAddCommGrpIso)
        (fun f => by
          ext a
          exact transferSectionsEquiv_comp k X a f)
    let e₀ := (J.sc p).mapHomologyIso ((CategoryTheory.evaluation _ _).obj V)
    let e₁ := corepresentedHomologyHomotopyAddEquiv G R c I p
    let S := (CochainComplex.singleFunctor (SheafWithTransfers.{u + 1} k) 0).obj R
    let q := HomotopyCategory.quotient (SheafWithTransfers.{u + 1} k) (.up ℤ)
    let e₂ := AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective (q.obj S) (I⟦p⟧))
    let e₃ := (CategoryTheory.Linear.homCongr ℤ
      (((DerivedCategory.quotientCompQhIso _).app S) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app R).symm)
      (((DerivedCategory.quotientCompQhIso _).app (I⟦p⟧)) ≪≫
        (DerivedCategory.Q.commShiftIso p).app I ≪≫ (shiftFunctor _ p).mapIso e)).toAddEquiv
    let a := e₀.symm.addCommGroupIsoToAddEquiv.trans (e₁.trans (e₂.trans e₃))
    let : Subsingleton ((DerivedCategory.singleFunctor _ 0).obj R ⟶ E⟦p⟧) := h X p
    exact AddCommGrpCat.isZero_iff_subsingleton.2 a.injective.subsingleton)
  have hH (p : ℤ) : IsZero ((DerivedCategory.homologyFunctor _ p).obj E) := by
    let A := PresheafWithTransfers.nisnevichSheafify k
    let B := SheafWithTransfers.forget k
    let L := ((B.mapHomologicalComplex (.up ℤ)).obj I)
    let e₀ : (PresheafWithTransfers.forget.obj (L.homology p)) ≅ J.homology p :=
      ((L.sc p).mapHomologyIso PresheafWithTransfers.forget).symm
    have hz : IsZero (L.homology p) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply PresheafWithTransfers.forget.map_injective
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 ((hJ p).of_iso e₀)
    let ε := asIso (PresheafWithTransfers.nisnevichSheafificationAdjunction k).counit
    let e₁ : A.obj (L.homology p) ≅ I.homology p :=
      ((L.sc p).mapHomologyIso A).symm ≪≫
        (HomologicalComplex.homologyFunctor _ (.up ℤ) p).mapIso
          ((NatIso.mapHomologicalComplex ε (.up ℤ)).app I ≪≫
            (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app I)
    let e₂ := (DerivedCategory.homologyFunctorFactors (SheafWithTransfers.{u + 1} k) p).app I
    exact ((A.map_isZero hz).of_iso e₁.symm).of_iso
      ((DerivedCategory.homologyFunctor _ p).mapIso e.symm ≪≫ e₂)
  let m : E ⟶ 0 := 0
  let : IsIso m := (DerivedCategory.isIso_iff _ _).2 (fun p =>
    (hH p).isIso ((DerivedCategory.homologyFunctor _ p).map_isZero (isZero_zero _)) _)
  exact (isZero_zero _).of_iso (asIso m)

/-- A derived map that is bijective on shifted Hom out of each original
smooth transfer representable is an isomorphism. -/
theorem isIso_of_bijective_hom_transferRepresentable
    {E L : DerivedCategory (SheafWithTransfers.{u + 1} k)} (f : E ⟶ L)
    (h : ∀ (X : Cor k) (p : ℤ), Function.Bijective (fun a :
      (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj X) ⟶ E⟦p⟧ =>
      a ≫ f⟦p⟧')) :
    IsIso f := by
  obtain ⟨M, g, δ, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g δ
  apply (T.isZero₃_iff_isIso₁ hT).1
  apply isZero_of_subsingleton_hom_transferRepresentable k
  intro X p
  let S := (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj X)
  let Tp := (shiftFunctor (Triangle (DerivedCategory (SheafWithTransfers.{u + 1} k))) p).obj T
  have hTp : Tp ∈ distTriang _ := T.shift_distinguished hT p
  refine ⟨fun (x y : S ⟶ M⟦p⟧) => sub_eq_zero.mp ?_⟩
  let a := x - y
  let e₁ : (E⟦p⟧)⟦(1 : ℤ)⟧ ≅ E⟦p + 1⟧ :=
    (shiftFunctorAdd _ p 1).symm.app E
  let e₂ : (L⟦p⟧)⟦(1 : ℤ)⟧ ≅ L⟦p + 1⟧ :=
    (shiftFunctorAdd _ p 1).symm.app L
  have hδ : (a ≫ Tp.mor₃) ≫ e₁.hom = 0 := by
    apply (h X (p + 1)).1
    change ((a ≫ Tp.mor₃) ≫ e₁.hom) ≫ f⟦p + 1⟧' = 0 ≫ f⟦p + 1⟧'
    have he : e₁.hom ≫ f⟦p + 1⟧' = (f⟦p⟧')⟦(1 : ℤ)⟧' ≫ e₂.hom :=
      ((shiftFunctorAdd (DerivedCategory (SheafWithTransfers.{u + 1} k)) p 1).inv.naturality f).symm
    have hz : p.negOnePow • (Tp.mor₃ ≫ (f⟦p⟧')⟦(1 : ℤ)⟧') = 0 := by
      have ht := comp_distTriang_mor_zero₃₁ Tp hTp
      change Tp.mor₃ ≫ ((p.negOnePow • f⟦p⟧')⟦(1 : ℤ)⟧') = 0 at ht
      simpa only [Functor.map_units_smul, Linear.comp_units_smul] using ht
    have hzero : Tp.mor₃ ≫ (f⟦p⟧')⟦(1 : ℤ)⟧' = 0 := by
      have hcancel := congrArg (p.negOnePow⁻¹ • ·) hz
      simpa only [smul_smul, inv_mul_cancel, one_smul, smul_zero] using hcancel
    calc
      _ = a ≫ (Tp.mor₃ ≫ (f⟦p⟧')⟦(1 : ℤ)⟧') ≫ e₂.hom := by
        simp only [Category.assoc, he]
      _ = _ := by simp only [hzero, comp_zero, zero_comp]
  have ha : a ≫ Tp.mor₃ = 0 := (cancel_mono e₁.hom).1
    (hδ.trans (show (0 : S ⟶ Tp.obj₁⟦(1 : ℤ)⟧) ≫ e₁.hom = 0 from zero_comp).symm)
  obtain ⟨b, hb⟩ := Tp.coyoneda_exact₃ hTp a ha
  obtain ⟨c, hc⟩ := (h X p).2 b
  change a = b ≫ (p.negOnePow • g⟦p⟧') at hb
  change a = 0
  have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT
  rw [hb, ← hc, Linear.comp_units_smul, Category.assoc, ← Functor.map_comp,
    hfg, Functor.map_zero, comp_zero, smul_zero]

end AlgebraicGeometry.SheafWithTransfers
