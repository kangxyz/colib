/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.SingleCoproduct
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjective
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.RepresentableUnit
import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition

/-!
# The reduced projective tensor of a single representable

The original degree-zero projective representable computes the
derived tensor. The actual projective quotient becomes the original
degree-zero target-unit quotient in that model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "A" => nisnevichSheafify k
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "L" => parameterTensorFunctor Gₘ
local notation "N" => reducedParameterTensorFunctor k

/-- The literal degree-zero representable in the bounded-above
derived category of transfer presheaves. -/
abbrev singleTransferRepresentable (Y : Cor k) : DerivedCategory.Minus PST :=
  (singleDerivedMinus k 0).obj ((representableLarge k).obj Y)

/-- The literal degree-zero sheafification of the original target-unit quotient. -/
abbrev singleTorusCancellationSheaf (Y : Cor k) : DerivedCategory.Minus NST :=
  DerivedCategory.Minus.ofCochainComplex
    ((CochainComplex.singleFunctor NST 0).obj ((A).obj (torusCancellationCoefficients k Y))) 0

/-- The chosen projective representative compared with the original
degree-zero projective representable. -/
@[no_expose]
def projectiveSingleRepresentativeIso (Y : Cor k) :
    ((boundedAboveProjectiveEquivalence k).inverse.obj (singleTransferRepresentable k Y)) ≅
      projectiveRepresentableSingle k Y := by
  let E := boundedAboveProjectiveEquivalence k
  let P := projectiveRepresentableSingle k Y
  let K := (CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)
  let e : E.functor.obj P ≅ singleTransferRepresentable k Y :=
    ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso PST).app K)
  exact E.inverse.mapIso e.symm ≪≫ (E.unitIso.app P).symm

omit [HasDerivedCategory NST] in
/-- After localization, the original projective representative comparison
is the counit of the chosen projective model. -/
theorem projectiveSingleRepresentativeIso_hom (Y : Cor k) :
    let E := boundedAboveProjectiveEquivalence k
    let X := singleTransferRepresentable k Y
    let K := (CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)
    let D := DerivedCategory.Minus.ι (C := PST)
    DerivedCategory.Qh.map (projectiveSingleRepresentativeIso k Y).hom.hom ≫
        (DerivedCategory.quotientCompQhIso PST).hom.app K =
      D.map (E.counitIso.hom.app X) := by
  intro E X K D
  let P := projectiveRepresentableSingle k Y
  let e : E.functor.obj P ≅ X :=
    ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso PST).app K)
  change D.map (E.functor.map (projectiveSingleRepresentativeIso k Y).hom) ≫ D.map e.hom = _
  have h : E.functor.map (projectiveSingleRepresentativeIso k Y).hom ≫ e.hom =
      E.counitIso.hom.app X := by
    unfold projectiveSingleRepresentativeIso
    change E.functor.map (E.inverse.map e.inv ≫ E.unitIso.inv.app P) ≫ e.hom = _
    rw [E.functor.map_comp, ← E.counit_app_functor P]
    have hn : E.functor.map (E.inverse.map e.inv) ≫ E.counitIso.hom.app (E.functor.obj P) =
        E.counitIso.hom.app X ≫ e.inv := E.counit_naturality e.inv
    rw [Category.assoc, reassoc_of% hn, e.inv_hom_id, Category.comp_id]
  exact (D.map_comp _ _).symm.trans (D.congr_map h)

/-- Applying a coefficient functor to the same projective comparison. -/
@[no_expose]
def projectiveSingleCoefficientIso (F : PST ⥤ PST) [F.Additive] (Y : Cor k) :
    ((projectiveDerivedMinusFunctor k F).obj (singleTransferRepresentable k Y)).obj ≅
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory c).obj (projectiveRepresentableSingle k Y).obj) :=
  DerivedCategory.Minus.ι.mapIso
    ((projectiveHomotopyMapToDerivedMinus k F).mapIso (projectiveSingleRepresentativeIso k Y))

/-- The actual sheafified cochain model of a coefficient functor on the
original projective representable. -/
@[no_expose]
def projectiveSingleTensorModelIso (F : PST ⥤ PST) [F.Additive] (Y : Cor k) :
    ((projectiveDerivedMinusFunctor k F ⋙ (A).mapDerivedCategoryMinus).obj
      (singleTransferRepresentable k Y)).obj ≅
      DerivedCategory.Q.obj (((F ⋙ A).mapHomologicalComplex c).obj
        ((CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y))) := by
  let C := (CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)
  let D := (F.mapHomologicalComplex c).obj C
  let e := ((A).mapDerivedCategoryFactorsh).app ((F.mapHomotopyCategory c).obj
    (projectiveRepresentableSingle k Y).obj)
  exact ((A).mapDerivedCategory.mapIso (projectiveSingleCoefficientIso k F Y)) ≪≫ e ≪≫
    (DerivedCategory.quotientCompQhIso NST).app (((A).mapHomologicalComplex c).obj D)

/-- The original cochain quotient on the projective degree-zero
representable, after actual Nisnevich sheafification. -/
def reducedTorusTensorSingleRepresentableIso (Y : Cor k) :
    ((N ⋙ A).mapHomologicalComplex c).obj
        ((CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)) ≅
      (CochainComplex.singleFunctor NST 0).obj ((A).obj (torusCancellationCoefficients k Y)) :=
  ((A).mapHomologicalComplex c).mapIso (reducedParameterTensorSingleRepresentableIso k Y 0) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex A c (0 : ℤ)).app
      (torusCancellationCoefficients k Y)

/-- The original projective tensor of a degree-zero representable is
its actual target-unit quotient in degree zero. -/
@[no_expose]
def projectiveReducedTorusRepresentableSingleIso (Y : Cor k) :
    (projectiveReducedTorusTensorToDerivedMinus k).obj (singleTransferRepresentable k Y) ≅
      singleTorusCancellationSheaf k Y :=
  ObjectProperty.isoMk _ (projectiveSingleTensorModelIso k N Y ≪≫
    DerivedCategory.Q.mapIso (reducedTorusTensorSingleRepresentableIso k Y))

/-- The unreduced projective model comparison on the same original
degree-zero representable. -/
@[no_expose]
def projectiveTorusRepresentableSingleModelIso (Y : Cor k) :
    ((projectiveTorusTensorToDerivedMinus k).obj (singleTransferRepresentable k Y)).obj ≅
      DerivedCategory.Q.obj (((L ⋙ A).mapHomologicalComplex c).obj
        ((CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y))) :=
  projectiveSingleTensorModelIso k L Y

/-- The unreduced comparison uses the same chosen-to-original projective
map and the original cochain localization. -/
theorem projectiveTorusRepresentableSingleModelIso_hom (Y : Cor k) :
    let K := (CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)
    let P := projectiveRepresentableSingle k Y
    let d := projectiveSingleRepresentativeIso k Y
    (projectiveTorusRepresentableSingleModelIso k Y).hom =
      (projectiveTensorModel k).map d.hom ≫
        (projectiveTensorModelIso k).hom.app P ≫
        (DerivedCategory.quotientCompQhIso NST).hom.app
          (((L ⋙ A).mapHomologicalComplex c).obj K) := by
  intro K P d
  let M := (L ⋙ A).mapHomotopyCategory c
  let J := (projInclusion k).obj P
  have h : (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ A)) c).hom.app J =
      𝟙 (M.obj J) := by
    rw [mapHomotopyCategoryCompIso_hom_app]
    change (HomotopyCategory.quotient NST c).map
      ((NatTrans.mapHomologicalComplex (𝟙 (L ⋙ A)) c).app J.as) = _
    rw [NatTrans.mapHomologicalComplex_id]
    exact (HomotopyCategory.quotient NST c).map_id _
  let q := DerivedCategory.Qh (C := NST)
  let e := (A).mapDerivedCategoryFactorsh
  let b := (DerivedCategory.quotientCompQhIso NST).hom.app
    (((L ⋙ A).mapHomologicalComplex c).obj K)
  let eP := e.hom.app (((L).mapHomotopyCategory c).obj J)
  have hh : (projectiveTensorModelIso k).hom.app P = eP := by
    unfold projectiveTensorModelIso
    change eP ≫ q.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ A)) c).hom.app J) = _
    rw [h]
    exact (congrArg (eP ≫ ·) (q.map_id (M.obj J))).trans (Category.comp_id eP)
  have hm : (projectiveTorusRepresentableSingleModelIso k Y).hom =
      (projectiveTensorModel k).map d.hom ≫ eP ≫ b := by
    unfold projectiveTorusRepresentableSingleModelIso projectiveSingleTensorModelIso
      projectiveSingleCoefficientIso
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    rfl
  calc
    _ = _ := hm
    _ = _ := congrArg (fun f => (projectiveTensorModel k).map d.hom ≫ f ≫ b) hh.symm

private theorem projectiveSingleTensorModelIso_naturality {F G : PST ⥤ PST}
    [F.Additive] [G.Additive] (η : F ⟶ G) (Y : Cor k) :
    ((Functor.whiskerRight (projectiveCoefficientNatTrans k η) (A).mapDerivedCategoryMinus).app
        (singleTransferRepresentable k Y)).hom ≫
        (projectiveSingleTensorModelIso k G Y).hom =
      (projectiveSingleTensorModelIso k F Y).hom ≫
        DerivedCategory.Q.map (((Functor.whiskerRight η A).mapHomologicalComplex c).app
          ((CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y))) := by
  let E := (boundedAboveProjectiveEquivalence k).inverse
  let P := projectiveRepresentableSingle k Y
  let C := (CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)
  let H' := HomotopyCategory.quotient NST c
  let U := (A).mapDerivedCategory
  let Q : CochainComplex NST ℤ ⥤ DerivedCategory NST := DerivedCategory.Q
  let e := (A).mapDerivedCategoryFactorsh
  let b := (DerivedCategory.quotientCompQhIso NST).hom
  let d := projectiveSingleRepresentativeIso k Y
  let t := η.mapHomotopyCategory c
  let f := (F.mapHomotopyCategory c).map d.hom.hom
  let g := (G.mapHomotopyCategory c).map d.hom.hom
  let v := t.app (E.obj (singleTransferRepresentable k Y)).obj
  let w := t.app P.obj
  let x := ((Functor.whiskerRight η A).mapHomologicalComplex c).app C
  have h₀ : v ≫ g = f ≫ w := (t.naturality d.hom.hom).symm
  have h₁ : U.map (DerivedCategory.Qh.map w) ≫
      e.hom.app ((G.mapHomotopyCategory c).obj P.obj) =
      e.hom.app ((F.mapHomotopyCategory c).obj P.obj) ≫
        DerivedCategory.Qh.map (H'.map x) := by
    exact e.hom.naturality w
  have h₂ : DerivedCategory.Qh.map (H'.map x) ≫
      b.app (((G ⋙ A).mapHomologicalComplex c).obj C) =
      b.app (((F ⋙ A).mapHomologicalComplex c).obj C) ≫ Q.map x :=
    b.naturality x
  let X := singleTransferRepresentable k Y
  let Qh := DerivedCategory.Qh (C := PST)
  let eF := e.hom.app ((F.mapHomotopyCategory c).obj P.obj)
  let eG := e.hom.app ((G.mapHomotopyCategory c).obj P.obj)
  let bF := b.app (((F ⋙ A).mapHomologicalComplex c).obj C)
  let bG := b.app (((G ⋙ A).mapHomologicalComplex c).obj C)
  have he (D : PST ⥤ PST) [D.Additive] :
      (projectiveSingleTensorModelIso k D Y).hom =
        U.map (Qh.map ((D.mapHomotopyCategory c).map d.hom.hom)) ≫
          e.hom.app ((D.mapHomotopyCategory c).obj P.obj) ≫
          b.app (((D ⋙ A).mapHomologicalComplex c).obj C) := by
    unfold projectiveSingleTensorModelIso projectiveSingleCoefficientIso
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    rfl
  let τ := Functor.whiskerRight (projectiveCoefficientNatTrans k η) (A).mapDerivedCategoryMinus
  have hv : (τ.app X).hom = U.map (Qh.map v) := by
    have h := projectiveCoefficientNatTrans_app_hom k η X
    exact U.congr_map h
  calc
    _ = U.map (Qh.map v) ≫ U.map (Qh.map g) ≫ eG ≫ bG :=
      congrArg₂ (· ≫ ·) hv (he G)
    _ = U.map (Qh.map (v ≫ g)) ≫ eG ≫ bG := by
      rw [← U.map_comp_assoc, ← Qh.map_comp]
    _ = U.map (Qh.map (f ≫ w)) ≫ eG ≫ bG :=
      congrArg (fun a => U.map (Qh.map a) ≫ eG ≫ bG) h₀
    _ = U.map (Qh.map f) ≫ (U.map (Qh.map w) ≫ eG) ≫ bG := by
      rw [Qh.map_comp, U.map_comp]
      simp only [Category.assoc]
    _ = U.map (Qh.map f) ≫ (eF ≫ DerivedCategory.Qh.map (H'.map x)) ≫ bG :=
      congrArg (fun a => U.map (Qh.map f) ≫ a ≫ bG) h₁
    _ = U.map (Qh.map f) ≫ eF ≫ bF ≫ Q.map x := by
      simp only [Category.assoc]
      rw [h₂]
    _ = (U.map (Qh.map f) ≫ eF ≫ bF) ≫ Q.map x := by
      simp only [Category.assoc]
    _ = _ := congrArg (· ≫ Q.map x) (he F).symm

/-- After the canonical projective representative comparison, the
derived quotient is exactly the original single target-unit quotient. -/
@[reassoc]
theorem projectiveReducedTorusRepresentableSingleIso_quotient (Y : Cor k) :
    ((projectiveReducedTorusTensorQuotient k).app (singleTransferRepresentable k Y)).hom ≫
        (projectiveReducedTorusRepresentableSingleIso k Y).hom.hom =
      (projectiveTorusRepresentableSingleModelIso k Y).hom ≫
        DerivedCategory.Q.map (torusTensorRepresentableSingleQuotient k Y) := by
  let η := reducedParameterTensorQuotient k
  let C := (CochainComplex.singleFunctor PST 0).obj ((representableLarge k).obj Y)
  let e := reducedTorusTensorSingleRepresentableIso k Y
  let f := ((Functor.whiskerRight η A).mapHomologicalComplex c).app C
  let Q : CochainComplex NST ℤ ⥤ DerivedCategory NST := DerivedCategory.Q
  let a := (A).mapHomologicalComplex c
  let j := HomologicalComplex.singleMapHomologicalComplex A c (0 : ℤ)
  let p := (parameterTensorRepresentableIso Gₘ Y).hom ≫ toTorusCancellationCoefficients k Y
  let R := (CochainComplex.singleFunctor PST 0)
  let S := (CochainComplex.singleFunctor NST 0)
  let d := HomologicalComplex.singleMapHomologicalComplex L c (0 : ℤ)
  let d' := HomologicalComplex.singleMapHomologicalComplex (L ⋙ A) c (0 : ℤ)
  have h : f ≫ e.hom = torusTensorRepresentableSingleQuotient k Y := by
    change a.map ((η.mapHomologicalComplex c).app C) ≫
        (a.map (reducedParameterTensorSingleRepresentableIso k Y 0).hom ≫ j.hom.app _) = _
    rw [← a.map_comp_assoc, reducedParameterTensorSingleRepresentableIso_quotient]
    let P := (representableLarge k).obj Y
    have hd : d'.hom.app P = a.map (d.hom.app P) ≫ j.hom.app ((L).obj P) := by
      rw [HomologicalComplex.singleMapHomologicalComplex_comp_hom_app]
      exact Category.id_comp _
    have hn : a.map (R.map p) ≫ j.hom.app _ = j.hom.app ((L).obj P) ≫ S.map ((A).map p) :=
      j.hom.naturality p
    change a.map (d.hom.app P ≫ R.map p) ≫ j.hom.app _ =
      d'.hom.app P ≫ S.map ((A).map p)
    rw [a.map_comp, Category.assoc, hn, hd, Category.assoc]
  let X := singleTransferRepresentable k Y
  let τ := Functor.whiskerRight (projectiveCoefficientNatTrans k η) (A).mapDerivedCategoryMinus
  let m := (projectiveSingleTensorModelIso k N Y).hom
  let l := (projectiveSingleTensorModelIso k L Y).hom
  have hn : (τ.app X).hom ≫ m = l ≫ Q.map f :=
    projectiveSingleTensorModelIso_naturality k η Y
  calc
    _ = ((τ.app X).hom ≫ m) ≫ Q.map e.hom := by
      unfold projectiveReducedTorusRepresentableSingleIso
      change (τ.app X).hom ≫ m ≫ Q.map e.hom = _
      exact (Category.assoc _ _ _).symm
    _ = (l ≫ Q.map f) ≫ Q.map e.hom :=
      congrArg (· ≫ Q.map e.hom) hn
    _ = l ≫ Q.map (torusTensorRepresentableSingleQuotient k Y) := by
      rw [Category.assoc, ← Q.map_comp, h]
    _ = _ := rfl

end AlgebraicGeometry.SheafWithTransfers
