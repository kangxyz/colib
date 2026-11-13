/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingularDerived
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import StacksCore.Algebra.Homology.TotalComplexHomotopy

/-!
# Singularization before Nisnevich sheafification

The original singular total complex preserves the coefficient bound,
homotopies, and quasi-isomorphisms. Its degree-zero inclusion gives
the unit on the actual bounded-above derived category.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

local notation "c" => ComplexShape.up ℤ

private def quotientFunctor :
    CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ ⥤
      HomotopyCategory (PresheafWithTransfers.{u + 1} k) c := HomotopyCategory.quotient _ _

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private theorem exists_bounded_cochain
    (K : HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    ∃ (L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ), L.IsStrictlyLE b ∧
      (quotientFunctor k).obj L = K.obj := by
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
  have h := K.property
  rw [← hL, HomotopyCategory.minus_quotient_obj_iff, CochainComplex.minus_iff] at h
  obtain ⟨b, h⟩ := h
  exact ⟨L, b, h, hL⟩

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private def singularHomotopy :
    HomotopyCategory (PresheafWithTransfers.{u + 1} k) c ⥤
      HomotopyCategory (PresheafWithTransfers.{u + 1} k) c :=
  CategoryTheory.Quotient.lift (homotopic _ c) (singularTotalFunctor k ⋙ quotientFunctor k)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _
      (HomologicalComplex₂.totalMapHomotopy₁ ((singularCochainFunctor 0).mapHomotopy h) c))

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private def singularHomotopyMinus :
    HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (HomotopyCategory.minus _).lift (HomotopyCategory.Minus.ι _ ⋙ singularHomotopy k)
    (fun K => by
      obtain ⟨L, b, hb, e⟩ := exists_bounded_cochain k K
      let : L.IsStrictlyLE b := hb
      have h : HomotopyCategory.minus _
          ((quotientFunctor k).obj ((singularTotalFunctor k).obj L)) :=
        (HomotopyCategory.minus_quotient_obj_iff _).2 ((CochainComplex.minus_iff _).2
          ⟨b, singularTotalFunctor_obj_isStrictlyLE k L b⟩)
      change HomotopyCategory.minus _ ((singularHomotopy k).obj K.obj)
      exact e ▸ h)

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private def singularHomotopyUnit : 𝟭 _ ⟶ singularHomotopy k :=
  CategoryTheory.Quotient.natTransLift (homotopic _ c)
    ((Functor.rightUnitor (quotientFunctor k)).hom ≫
      Functor.whiskerRight (singularTotalUnit k) (quotientFunctor k))

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private def singularHomotopyMinusUnit : 𝟭 _ ⟶ singularHomotopyMinus k where
  app K := ObjectProperty.homMk ((singularHomotopyUnit k).app K.obj)
  naturality _ _ f := by
    apply (HomotopyCategory.Minus.ι (PresheafWithTransfers.{u + 1} k)).map_injective
    exact (singularHomotopyUnit k).naturality f.hom

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private theorem singularHomotopyMinus_preserves_quasiIso :
    ∀ {X Y} (f : X ⟶ Y), transferHomotopyMinusQuasiIso k f →
      transferHomotopyMinusQuasiIso k ((singularHomotopyMinus k).map f) := by
  intro X Y f hf
  obtain ⟨K₀, a, ha, e⟩ := exists_bounded_cochain k X
  obtain ⟨L₀, b, hb, d⟩ := exists_bounded_cochain k Y
  let q := quotientFunctor k
  let : q.Full := inferInstanceAs ((HomotopyCategory.quotient (PresheafWithTransfers.{u + 1} k)
    c).Full)
  let g : q.obj K₀ ⟶ q.obj L₀ := eqToHom e ≫ f.hom ≫ eqToHom d.symm
  obtain ⟨f₀, h₀⟩ := q.map_surjective g
  let W := HomotopyCategory.quasiIso (PresheafWithTransfers.{u + 1} k) c
  have hg : W g := W.comp_mem _ _ (W.of_isIso _)
    (W.comp_mem _ _ hf (W.of_isIso _))
  have hq : QuasiIso f₀ := by
    have hh : W (q.map f₀) := h₀.symm ▸ hg
    exact (HomologicalComplex.mem_quasiIso_iff f₀).1
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f₀).1 hh)
  let : K₀.IsStrictlyLE a := ha
  let : L₀.IsStrictlyLE b := hb
  let : K₀.IsStrictlyLE (max a b) := K₀.isStrictlyLE_of_le a _ (le_max_left _ _)
  let : L₀.IsStrictlyLE (max a b) := L₀.isStrictlyLE_of_le b _ (le_max_right _ _)
  let : QuasiIso f₀ := hq
  have hc : QuasiIso ((singularTotalFunctor k).map f₀) :=
    singularTotalFunctor_quasiIso f₀ (max a b)
  have hS : W ((singularHomotopy k).map g) := by
    rw [← h₀]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      ((HomologicalComplex.mem_quasiIso_iff _).2 hc)
  let F := singularHomotopy k
  change W (F.map f.hom)
  have hff : F.map f.hom = F.map (eqToHom e.symm) ≫ F.map g ≫ F.map (eqToHom d) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    simp [g]
  rw [hff]
  exact W.comp_mem _ _ (W.of_isIso _) (W.comp_mem _ _ hS (W.of_isIso _))

private theorem singularHomotopyToMinus_inverts :
    (transferHomotopyMinusQuasiIso k).IsInvertedBy
      (singularHomotopyMinus k ⋙ transferHomotopyMinusLocalization k) := by
  intro X Y f hf
  exact Localization.inverts (transferHomotopyMinusLocalization k)
    (transferHomotopyMinusQuasiIso k) _ (singularHomotopyMinus_preserves_quasiIso k f hf)

/-- The original total singular endofunctor on bounded-above transfer presheaves. -/
def singularPresheafDerivedFunctor :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  Localization.lift (singularHomotopyMinus k ⋙ transferHomotopyMinusLocalization k)
    (singularHomotopyToMinus_inverts k) (transferHomotopyMinusLocalization k)

private def singularPresheafDerivedFactors :
    transferHomotopyMinusLocalization k ⋙ singularPresheafDerivedFunctor k ≅
      singularHomotopyMinus k ⋙ transferHomotopyMinusLocalization k :=
  Localization.fac (singularHomotopyMinus k ⋙ transferHomotopyMinusLocalization k)
    (singularHomotopyToMinus_inverts k) (transferHomotopyMinusLocalization k)

private instance singularPresheafDerivedLifting :
    Localization.Lifting (transferHomotopyMinusLocalization k) (transferHomotopyMinusQuasiIso k)
      (singularHomotopyMinus k ⋙ transferHomotopyMinusLocalization k)
      (singularPresheafDerivedFunctor k) :=
  ⟨singularPresheafDerivedFactors k⟩

/-- The original cochain augmentation, descended through the native derived quotient. -/
def singularPresheafDerivedUnit : 𝟭 _ ⟶ singularPresheafDerivedFunctor k :=
  Localization.liftNatTrans (transferHomotopyMinusLocalization k) (transferHomotopyMinusQuasiIso k)
    (transferHomotopyMinusLocalization k)
    (singularHomotopyMinus k ⋙ transferHomotopyMinusLocalization k)
    (𝟭 _) (singularPresheafDerivedFunctor k)
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (singularHomotopyMinusUnit k) (transferHomotopyMinusLocalization k))

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private def boundedHomotopyCochain (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] : HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  ⟨(quotientFunctor k).obj K,
    (HomotopyCategory.minus_quotient_obj_iff _).2 ((CochainComplex.minus_iff _).2
      ⟨b, inferInstance⟩)⟩

/-- The original cochain complex as an object of the bounded-above localization. -/
def singularPresheafDerivedCochainObj
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (transferHomotopyMinusLocalization k).obj (boundedHomotopyCochain k K b)

/-- The original map of bounded-above cochains in their native localization. -/
def singularPresheafDerivedCochainMap
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b] :
    singularPresheafDerivedCochainObj k K a ⟶ singularPresheafDerivedCochainObj k L b :=
  (transferHomotopyMinusLocalization k).map
    (ObjectProperty.homMk ((quotientFunctor k).map f))

/-- In the unbounded derived category the representative is the original quotient. -/
def singularPresheafDerivedCochainToQIso
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    DerivedCategory.Minus.ι.obj (singularPresheafDerivedCochainObj k K b) ≅
      DerivedCategory.Q.obj K :=
  (transferHomotopyMinusLocalizationIso k).app (boundedHomotopyCochain k K b) ≪≫
    (DerivedCategory.quotientCompQhIso _).app K

@[reassoc]
theorem singularPresheafDerivedCochainToQIso_naturality
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b] :
    (DerivedCategory.Minus.ι).map (singularPresheafDerivedCochainMap k f a b) ≫
        (singularPresheafDerivedCochainToQIso k L b).hom =
      (singularPresheafDerivedCochainToQIso k K a).hom ≫ DerivedCategory.Q.map f := by
  let e := transferHomotopyMinusLocalizationIso k
  let d := DerivedCategory.quotientCompQhIso (PresheafWithTransfers.{u + 1} k)
  let g : boundedHomotopyCochain k K a ⟶ boundedHomotopyCochain k L b :=
    ObjectProperty.homMk ((quotientFunctor k).map f)
  change (DerivedCategory.Minus.ι).map ((transferHomotopyMinusLocalization k).map g) ≫
      e.hom.app _ ≫ d.hom.app L = (e.hom.app _ ≫ d.hom.app K) ≫ DerivedCategory.Q.map f
  have he : (DerivedCategory.Minus.ι).map ((transferHomotopyMinusLocalization k).map g) ≫
      e.hom.app (boundedHomotopyCochain k L b) =
        e.hom.app (boundedHomotopyCochain k K a) ≫
          DerivedCategory.Qh.map ((quotientFunctor k).map f) :=
    e.hom.naturality g
  calc
    _ = (_ ≫ e.hom.app (boundedHomotopyCochain k L b)) ≫ d.hom.app L :=
      (Category.assoc _ _ _).symm
    _ = (e.hom.app (boundedHomotopyCochain k K a) ≫
        DerivedCategory.Qh.map ((quotientFunctor k).map f)) ≫ d.hom.app L :=
      congrArg (· ≫ d.hom.app L) he
    _ = e.hom.app (boundedHomotopyCochain k K a) ≫ (d.hom.app K ≫ DerivedCategory.Q.map f) :=
      (Category.assoc _ _ _).trans
        (congrArg (e.hom.app (boundedHomotopyCochain k K a) ≫ ·) (d.hom.naturality f))
    _ = _ := (Category.assoc _ _ _).symm

local instance (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : ((singularTotalFunctor k).obj K).IsStrictlyLE b :=
  singularTotalFunctor_obj_isStrictlyLE k K b

/-- The localization comparison with the original singular total complex. -/
def singularPresheafDerivedCochainIso
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    (singularPresheafDerivedFunctor k).obj (singularPresheafDerivedCochainObj k K b) ≅
      singularPresheafDerivedCochainObj k ((singularTotalFunctor k).obj K) b :=
  (singularPresheafDerivedFactors k).app (boundedHomotopyCochain k K b)

@[reassoc]
theorem singularPresheafDerivedCochainIso_unit
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    (singularPresheafDerivedUnit k).app (singularPresheafDerivedCochainObj k K b) ≫
        (singularPresheafDerivedCochainIso k K b).hom =
      singularPresheafDerivedCochainMap k (singularTotalUnitApp k K) b b := by
  unfold singularPresheafDerivedUnit singularPresheafDerivedCochainObj
  rw [Localization.liftNatTrans_app]
  let Q := transferHomotopyMinusLocalization k
  let X := boundedHomotopyCochain k K b
  let e := singularPresheafDerivedCochainIso k K b
  let f := singularPresheafDerivedCochainMap k (singularTotalUnitApp k K) b b
  change ((Q.rightUnitor.hom.app X ≫
      (Q.leftUnitor.inv.app X ≫ f) ≫ e.inv) ≫ e.hom) = f
  simp only [Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact Category.id_comp f

@[reassoc]
theorem singularPresheafDerivedCochainIso_naturality
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b] :
    (singularPresheafDerivedFunctor k).map (singularPresheafDerivedCochainMap k f a b) ≫
        (singularPresheafDerivedCochainIso k L b).hom =
      (singularPresheafDerivedCochainIso k K a).hom ≫
        singularPresheafDerivedCochainMap k ((singularTotalFunctor k).map f) a b :=
  (singularPresheafDerivedFactors k).hom.naturality
    (ObjectProperty.homMk (X := boundedHomotopyCochain k K a)
      (Y := boundedHomotopyCochain k L b) ((quotientFunctor k).map f))

/-- A bounded-above object admits a representative using the same specified bound. -/
theorem exists_singularPresheafDerivedCochainObj_iso
    (X : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) (b : ℤ) (hX : X.obj.IsLE b) :
    ∃ (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (h : K.IsStrictlyLE b),
      let _ : K.IsStrictlyLE b := h
      Nonempty (singularPresheafDerivedCochainObj k K b ≅ X) := by
  let : X.obj.IsLE b := hX
  obtain ⟨K, hK, ⟨e⟩⟩ := X.obj.exists_iso_Q_obj_of_isLE b
  let : K.IsStrictlyLE b := hK
  let d := singularPresheafDerivedCochainToQIso k K b ≪≫ e.symm
  exact ⟨K, hK, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso d⟩⟩

end AlgebraicGeometry.MotivicHomotopy
