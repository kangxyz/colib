/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedBaseSummand
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjective
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Reduced
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans

/-!
# Transposing the constant-torus projector

The two original mates of the base unit and projection give the
constant projector on the projective tensor. The corresponding
projector on the right is unit restriction followed by constant
sections. The derived Hom equivalence preserves these actual maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers Stacks.DerivedFunctor

variable (k : Type u) [Field k]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "S" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject S
local notation "A" => nisnevichSheafify k
local notation "F" => parameterTensorFunctor Gₘ
local notation "L" => F ⋙ A
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "R" => U ⋙ T

/-- The constant summand of the original left tensor is projection then unit. -/
def torusTensorBaseProjector : F ⟶ F :=
  torusParameterTensorProjection k ≫ torusParameterTensorUnit k

/-- The constant summand of exact torus reindexing is restriction then constants. -/
def torusPresheafBaseProjector : T ⟶ T :=
  torusPresheafUnitNatTrans k ≫ torusPresheafConstantNatTrans k

private theorem torusPresheafBaseProjector_app (P : PST) :
    (torusPresheafBaseProjector k).app P = torusUnit P ≫ torusConstant P := by
  change (torusUnit P ≫ (baseSectionsPresheafNatIso k).inv.app P) ≫
    (baseSectionsPresheafNatIso k).hom.app P ≫ torusConstant P = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem torusTensorBaseProjector_homEquiv
    {P : PST} {N : NST} (f : (L).obj P ⟶ N) :
    ((parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)).homEquiv P N
      (((A).map ((torusTensorBaseProjector k).app P)) ≫ f) =
    ((parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)).homEquiv P N f ≫
      (torusPresheafBaseProjector k).app ((U).obj N) := by
  let a := nisnevichSheafificationAdjunction k
  let t := parameterTensorAdjunction Gₘ
  let g := (a.homEquiv _ _) f
  rw [Adjunction.comp_homEquiv]
  change (t.homEquiv _ _) ((a.homEquiv _ _) ((A).map _ ≫ f)) =
    (t.homEquiv _ _) g ≫ _
  rw [Adjunction.homEquiv_naturality_left]
  change (t.homEquiv _ _) (((torusParameterTensorProjection k).app P ≫
      (torusParameterTensorUnit k).app P) ≫ g) = _
  rw [Category.assoc, torusParameterTensorProjection_homEquiv,
    torusParameterTensorUnit_homEquiv, torusPresheafBaseProjector_app, Category.assoc]

private abbrev leftCochainProjector :=
  (Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomologicalComplex c

private abbrev rightCochainProjector :=
  (Functor.whiskerLeft (U) (torusPresheafBaseProjector k)).mapHomologicalComplex c

private abbrev rightHomotopyProjector :=
  (Functor.whiskerLeft (U) (torusPresheafBaseProjector k)).mapHomotopyCategory c

private theorem torusLeftHomotopyProjector_app (X : HomotopyCategory PST c) :
    (((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomotopyCategory c).app X) =
      ((A).mapHomotopyCategory c).map
        (((torusTensorBaseProjector k).mapHomotopyCategory c).app X) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rfl

private theorem torusRightHomotopyProjector_app (I : HomotopyCategory NST c) :
    (rightHomotopyProjector k).app I =
      ((torusPresheafBaseProjector k).mapHomotopyCategory c).app
        (((U).mapHomotopyCategory c).obj I) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  rfl

private theorem torusTensorBaseProjector_cochain_homEquiv
    {P : CochainComplex PST ℤ} {I : CochainComplex NST ℤ}
    (f : ((L).mapHomologicalComplex c).obj P ⟶ I) :
    (torusTensorCochainAdjunction k).homEquiv P I ((leftCochainProjector k).app P ≫ f) =
    (torusTensorCochainAdjunction k).homEquiv P I f ≫
      (rightCochainProjector k).app I := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := torusTensorBaseProjector_homEquiv k (f.f i)
  change (((torusTensorCochainAdjunction k).homEquiv P I
        (((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomologicalComplex c).app P ≫
          f)).f i) =
    (((torusTensorCochainAdjunction k).homEquiv P I f).f i) ≫
      (torusPresheafBaseProjector k).app ((U).obj (I.X i))
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let adj := (parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)
  change adj.unit.app (P.X i) ≫ (R).map ((A).map
      ((torusTensorBaseProjector k).app (P.X i)) ≫ f.f i) =
    (adj.unit.app (P.X i) ≫ (R).map (f.f i)) ≫
      (torusPresheafBaseProjector k).app ((U).obj (I.X i))
  simpa only [Adjunction.homEquiv_unit] using h

private theorem torusTensorBaseProjector_homotopy_homEquiv
    {P : HomotopyCategory PST c} {I : HomotopyCategory NST c}
    (f : ((L).mapHomotopyCategory c).obj P ⟶ I) :
    (torusTensorHomotopyAdjunction k).homEquiv P I
      (((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomotopyCategory c).app P ≫
        f) =
    (torusTensorHomotopyAdjunction k).homEquiv P I f ≫
      (((Functor.whiskerLeft (U) (torusPresheafBaseProjector k)).mapHomotopyCategory c).app I) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  let Q := HomotopyCategory.quotient PST c
  let Q' := HomotopyCategory.quotient NST c
  change Q'.obj (((L).mapHomologicalComplex c).obj P) ⟶ Q'.obj I at f
  obtain ⟨f, rfl⟩ := Q'.map_surjective f
  let H := torusTensorHomotopyAdjunction k
  let A' := torusTensorCochainAdjunction k
  let l := (leftCochainProjector k).app P
  let r := (rightCochainProjector k).app I
  change H.homEquiv (Q.obj P) (Q'.obj I) (Q'.map l ≫ Q'.map f) =
    H.homEquiv (Q.obj P) (Q'.obj I) (Q'.map f) ≫ Q.map r
  have hl : H.homEquiv (Q.obj P) (Q'.obj I) (Q'.map (l ≫ f)) =
      Q.map (A'.homEquiv P I (l ≫ f)) :=
    torusTensorHomotopyAdjunction_homEquiv_quotient k (l ≫ f)
  have hf : H.homEquiv (Q.obj P) (Q'.obj I) (Q'.map f) = Q.map (A'.homEquiv P I f) :=
    torusTensorHomotopyAdjunction_homEquiv_quotient k (P := P) (I := I) f
  rw [← Q'.map_comp, hl, hf, ← Q.map_comp]
  exact Q.congr_map (torusTensorBaseProjector_cochain_homEquiv k (P := P) (I := I) f)

variable [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
variable [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

omit [HasDerivedCategory PST] in
private theorem torusLeftHomotopyCompIso_inv_map (X : HomotopyCategory PST c) :
    (DerivedCategory.Qh (C := NST)).map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl L) c).inv.app X) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  exact (DerivedCategory.Qh (C := NST)).map_id _

omit [HasDerivedCategory NST] in
private theorem torusRightHomotopyCompIso_inv_map (I : HomotopyCategory NST c) :
    (DerivedCategory.Qh (C := PST)).map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl R) c).inv.app I) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  exact (DerivedCategory.Qh (C := PST)).map_id _

set_option quotPrecheck false in
local notation "D" => (T).mapDerivedCategory
local notation "Dᵣ" => torusTensorDerivedRight k
local notation "Dₗ" => projectiveTorusTensorToDerivedMinus k ⋙ DerivedCategory.Minus.ι
set_option quotPrecheck false in
local notation "E" => (boundedAboveProjectiveEquivalence k).inverse
local notation "qᵢ" => torusTensorInjectiveToDerived k

/-- The original left tensor projector applied on the projective representatives. -/
def projectiveTorusBaseProjector :
    Dₗ ⟶ Dₗ :=
  Functor.whiskerRight (projectiveCoefficientNatTrans k (torusTensorBaseProjector k))
    ((A).mapDerivedCategoryMinus ⋙ DerivedCategory.Minus.ι)

private theorem projectiveTorusBaseProjector_factors (P : DerivedCategory.Minus PST) :
    (projectiveTensorModelIso k).inv.app ((E).obj P) ≫
        (projectiveTorusBaseProjector k).app P =
      DerivedCategory.Qh.map
        (((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomotopyCategory c).app
          ((E).obj P).obj) ≫
      (projectiveTensorModelIso k).inv.app ((E).obj P) := by
  let X := ((E).obj P).obj
  let m := ((torusTensorBaseProjector k).mapHomotopyCategory c).app X
  have h := ((A).mapDerivedCategoryFactorsh.inv.naturality m)
  have hcomp :
      ((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomotopyCategory c).app X =
        ((A).mapHomotopyCategory c).map m := torusLeftHomotopyProjector_app k X
  let n := (Functor.mapHomotopyCategoryCompIso (Iso.refl L) c).inv.app X
  let Q := DerivedCategory.Qh (C := NST)
  let a := (A).mapDerivedCategory
  let e := (A).mapDerivedCategoryFactorsh
  let l := ((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomotopyCategory c).app X
  have hn : Q.map n = 𝟙 _ := torusLeftHomotopyCompIso_inv_map k X
  have hp : a.map (((projectiveCoefficientNatTrans k (torusTensorBaseProjector k)).app P).hom) =
      a.map (DerivedCategory.Qh.map m) :=
    a.congr_map (projectiveCoefficientNatTrans_app_hom k (torusTensorBaseProjector k) P)
  unfold projectiveTorusBaseProjector projectiveTensorModelIso
  simp only [Functor.whiskerRight_app, Functor.comp_map, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv]
  change (Q.map n ≫ e.inv.app (((F).mapHomotopyCategory c).obj X)) ≫
      a.map (((projectiveCoefficientNatTrans k (torusTensorBaseProjector k)).app P).hom) =
    Q.map l ≫ (Q.map n ≫ e.inv.app (((F).mapHomotopyCategory c).obj X))
  rw [hn, hp]
  have hh : Q.map (((A).mapHomotopyCategory c).map m) ≫
      e.inv.app (((F).mapHomotopyCategory c).obj X) =
    e.inv.app (((F).mapHomotopyCategory c).obj X) ≫ a.map (DerivedCategory.Qh.map m) := h
  exact (congrArg (· ≫ a.map (DerivedCategory.Qh.map m)) (Category.id_comp _)).trans
    (hh.symm.trans ((congrArg (fun z => Q.map z ≫ e.inv.app
      (((F).mapHomotopyCategory c).obj X)) hcomp.symm).trans
      (congrArg (Q.map l ≫ ·) (Category.id_comp _).symm)))

private theorem torusTensorInjectiveReindexingIso_baseProjector
    (I : TorusTensorInjectiveHomotopy k) :
    DerivedCategory.Qh.map ((rightHomotopyProjector k).app I.obj) ≫
      (torusTensorInjectiveReindexingIso k).hom.app I =
    (torusTensorInjectiveReindexingIso k).hom.app I ≫
      (mapDerivedNatTrans (torusPresheafBaseProjector k)).app ((forgetDerivedFunctor k).obj
        ((qᵢ).obj I)) := by
  let H := (U).mapHomotopyCategory c
  let β := mapDerivedNatTrans (torusPresheafBaseProjector k)
  let n := (Functor.mapHomotopyCategoryCompIso (Iso.refl R) c).inv.app I.obj
  let Q := DerivedCategory.Qh (C := PST)
  let e := (T).mapDerivedCategoryFactorsh.inv.app (H.obj I.obj)
  let η := (forgetHomotopyUnit k).app I.obj
  let a := ((torusPresheafBaseProjector k).mapHomotopyCategory c).app (H.obj I.obj)
  let b := β.app (Q.obj (H.obj I.obj))
  let b' := β.app ((forgetDerivedFunctor k).obj ((qᵢ).obj I))
  let f := (D).map η
  let g := (torusTensorInjectiveReindexingIso k).hom.app I
  have he : Q.map a ≫ e = e ≫ b :=
    Qh_map_comp_mapDerivedCategoryFactorsh_inv_app (torusPresheafBaseProjector k) (H.obj I.obj)
  have hcomp : (rightHomotopyProjector k).app I.obj = a :=
    torusRightHomotopyProjector_app k I.obj
  have hn : Q.map n = 𝟙 _ := torusRightHomotopyCompIso_inv_map k I.obj
  have hg : g = e ≫ f := by
    unfold g torusTensorInjectiveReindexingIso
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, NatTrans.comp_app,
      asIso_hom]
    change Q.map n ≫ e ≫ f = _
    rw [hn]
    exact Category.id_comp _
  have hβ : f ≫ b' = b ≫ f := β.naturality η
  change Q.map ((rightHomotopyProjector k).app I.obj) ≫ g = g ≫ b'
  rw [hcomp, hg]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ f) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (e ≫ ·) hβ.symm).trans (Category.assoc _ _ _).symm)))

private theorem projectiveTorusTensorDerivedHomEquiv_projector_on_model
    (P : DerivedCategory.Minus PST) (I : TorusTensorInjectiveHomotopy k)
    (f : (Dₗ).obj P ⟶ (qᵢ).obj I) :
    projectiveTorusTensorDerivedHomEquiv k P ((qᵢ).obj I)
        ((projectiveTorusBaseProjector k).app P ≫ f) =
      projectiveTorusTensorDerivedHomEquiv k P ((qᵢ).obj I) f ≫
        (mapDerivedNatTrans (torusPresheafBaseProjector k)).app
          ((forgetDerivedFunctor k).obj ((qᵢ).obj I)) := by
  let E₀ := (E).obj P
  let e := (projectiveTensorModelIso k).inv.app E₀
  let Q := DerivedCategory.Qh (C := NST)
  let d := (DerivedCategory.Minus.ι (C := PST)).mapIso
    ((boundedAboveProjectiveEquivalence k).counitIso.app P)
  let : CochainComplex.IsKInjective I.obj.as := I.property
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (((L).mapHomotopyCategory c).obj E₀.obj) I.obj.as).2 (e ≫ f)
  let p := (projectiveTorusBaseProjector k).app P
  let l :=
    ((Functor.whiskerRight (torusTensorBaseProjector k) (A)).mapHomotopyCategory c).app E₀.obj
  let H := torusTensorHomotopyAdjunction k
  let r := (rightHomotopyProjector k).app I.obj
  let t := (torusTensorInjectiveReindexingIso k).hom.app I
  let b := (mapDerivedNatTrans (torusPresheafBaseProjector k)).app
    ((forgetDerivedFunctor k).obj ((qᵢ).obj I))
  have hp : e ≫ p = Q.map l ≫ e := projectiveTorusBaseProjector_factors k P
  have hleft : e ≫ p ≫ f = Q.map (l ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f) hp).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (Q.map l ≫ ·) hg.symm).trans (Q.map_comp _ _).symm)))
  have hright : e ≫ f = Q.map g := hg.symm
  rw [projectiveTorusTensorDerivedHomEquiv_on_representatives k P I (p ≫ f),
    projectiveTorusTensorDerivedHomEquiv_on_representatives k P I f]
  change d.inv ≫ torusTensorHomEquivOnRepresentatives k E₀ I
    (e ≫ p ≫ f) = (d.inv ≫ torusTensorHomEquivOnRepresentatives k E₀ I (e ≫ f)) ≫ b
  rw [hleft, hright, tensorHomOnRepresentatives_map k E₀ I (l ≫ g),
    tensorHomOnRepresentatives_map k E₀ I g]
  let Q' := DerivedCategory.Qh (C := PST)
  let z := H.homEquiv E₀.obj I.obj g
  have h : H.homEquiv E₀.obj I.obj (l ≫ g) = z ≫ r :=
    torusTensorBaseProjector_homotopy_homEquiv k g
  have ht : Q'.map r ≫ t = t ≫ b := torusTensorInjectiveReindexingIso_baseProjector k I
  change d.inv ≫ Q'.map (H.homEquiv E₀.obj I.obj (l ≫ g)) ≫ t =
    (d.inv ≫ Q'.map z ≫ t) ≫ b
  rw [h, Q'.map_comp]
  simp only [Category.assoc]
  exact congrArg (d.inv ≫ Q'.map z ≫ ·) ht

omit [HasDerivedCategory NST] in
private theorem torusPresheafBaseProjector_derived :
    mapDerivedNatTrans (torusPresheafBaseProjector k) =
      torusPresheafDerivedUnitRestriction k ≫ torusPresheafDerivedConstant k := by
  let Q := DerivedCategory.Q (C := PST)
  let W := HomologicalComplex.quasiIso PST c
  apply Localization.natTrans_ext Q W
  intro J
  let e := (T).mapDerivedCategoryFactors.app J
  let ρ := torusPresheafUnitNatTrans k
  let σ := torusPresheafConstantNatTrans k
  have hf :
      (presheafComplexRestriction k).app J ≫ (presheafComplexConstant k).app J =
        (((torusPresheafBaseProjector k).mapHomologicalComplex c).app J) := by
    apply HomologicalComplex.hom_ext
    intro i
    change ρ.app (J.X i) ≫ σ.app (J.X i) = _
    rfl
  let a := (mapDerivedNatTrans (torusPresheafBaseProjector k)).app (Q.obj J)
  let q := Q.map (((torusPresheafBaseProjector k).mapHomologicalComplex c).app J)
  let r := (torusPresheafDerivedUnitRestriction k).app (Q.obj J)
  let s := (torusPresheafDerivedConstant k).app (Q.obj J)
  have h : a ≫ e.hom = e.hom ≫ q :=
    mapDerivedNatTrans_factors_app (torusPresheafBaseProjector k) J
  have hr : e.inv ≫ r = Q.map ((presheafComplexRestriction k).app J) :=
    torusPresheafDerivedUnitRestriction_app_Q_obj k J
  have hs : s = Q.map ((presheafComplexConstant k).app J) ≫ e.inv :=
    torusPresheafDerivedConstant_app_Q_obj k J
  apply (cancel_epi e.inv).1
  change e.inv ≫ a = e.inv ≫ r ≫ s
  calc
    _ = q ≫ e.inv := by
      calc
        _ = e.inv ≫ a ≫ e.hom ≫ e.inv := by
          exact (congrArg (e.inv ≫ ·) (Category.comp_id a).symm).trans
            (congrArg (fun z => e.inv ≫ a ≫ z) e.hom_inv_id).symm
        _ = e.inv ≫ (a ≫ e.hom) ≫ e.inv :=
          congrArg (e.inv ≫ ·) (Category.assoc _ _ _).symm
        _ = e.inv ≫ (e.hom ≫ q) ≫ e.inv :=
          congrArg (fun z => e.inv ≫ z ≫ e.inv) h
        _ = _ := (congrArg (e.inv ≫ ·) (Category.assoc _ _ _)).trans (e.inv_hom_id_assoc _)
    _ = (Q.map ((presheafComplexRestriction k).app J) ≫
        Q.map ((presheafComplexConstant k).app J)) ≫ e.inv := by
      rw [← Q.map_comp, hf]
    _ = _ := by
      rw [Category.assoc, ← hs, ← hr]
      exact Category.assoc _ _ _

/-- The original left projector transposes to the actual restriction followed
by constants on the exact derived presheaf torus functor. -/
theorem projectiveTorusTensorDerivedHomEquiv_baseProjector
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) (f : (Dₗ).obj P ⟶ K) :
    projectiveTorusTensorDerivedHomEquiv k P K ((projectiveTorusBaseProjector k).app P ≫ f) =
      projectiveTorusTensorDerivedHomEquiv k P K f ≫
        (torusPresheafDerivedUnitRestriction k).app ((forgetDerivedFunctor k).obj K) ≫
        (torusPresheafDerivedConstant k).app ((forgetDerivedFunctor k).obj K) := by
  let Q := DerivedCategory.Q (C := NST)
  let J := Q.objPreimage K
  obtain ⟨I, h, hI, hh⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck J
  let : QuasiIso h := hh
  let I₀ : TorusTensorInjectiveHomotopy k := ⟨(HomotopyCategory.quotient NST c).obj I, hI⟩
  let e : (qᵢ).obj I₀ ≅ K :=
    (DerivedCategory.quotientCompQhIso NST).app I ≪≫ (asIso (Q.map h)).symm ≪≫
      Q.objObjPreimageIso K
  let β := mapDerivedNatTrans (torusPresheafBaseProjector k)
  let R₀ := forgetDerivedFunctor k
  let a := (projectiveTorusBaseProjector k).app P
  have hK :
      projectiveTorusTensorDerivedHomEquiv k P K (a ≫ f) =
        projectiveTorusTensorDerivedHomEquiv k P K f ≫ β.app (R₀.obj K) := by
    let d := (Dᵣ).mapIso e.symm
    let K₀ := (qᵢ).obj I₀
    let x := projectiveTorusTensorDerivedHomEquiv k P K f
    let y := projectiveTorusTensorDerivedHomEquiv k P K (a ≫ f)
    let b := β.app (R₀.obj K)
    let b₀ := β.app (R₀.obj K₀)
    let t : (P.obj ⟶ (Dᵣ).obj K) ≃ (P.obj ⟶ (Dᵣ).obj K₀) := d.homToEquiv
    change y = x ≫ b
    apply t.injective
    change y ≫ d.hom = (x ≫ b) ≫ d.hom
    have hn : d.hom ≫ b₀ = b ≫ d.hom := β.naturality (R₀.map e.inv)
    have hy : y ≫ d.hom =
        projectiveTorusTensorDerivedHomEquiv k P K₀ (a ≫ f ≫ e.inv) := by
      exact (projectiveTorusTensorDerivedHomEquiv_postcompose k P (a ≫ f) e.inv).symm.trans
        (congrArg (projectiveTorusTensorDerivedHomEquiv k P K₀) (Category.assoc _ _ _))
    calc
      _ = projectiveTorusTensorDerivedHomEquiv k P K₀ (a ≫ f ≫ e.inv) := hy
      _ = projectiveTorusTensorDerivedHomEquiv k P K₀ (f ≫ e.inv) ≫ b₀ :=
        projectiveTorusTensorDerivedHomEquiv_projector_on_model k P I₀ (f ≫ e.inv)
      _ = (x ≫ d.hom) ≫ b₀ := congrArg (· ≫ b₀)
        (projectiveTorusTensorDerivedHomEquiv_postcompose k P f e.inv)
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (x ≫ ·) hn).trans (Category.assoc _ _ _).symm)
  rw [hK, show β = _ from torusPresheafBaseProjector_derived k, NatTrans.comp_app]

end AlgebraicGeometry.SheafWithTransfers
