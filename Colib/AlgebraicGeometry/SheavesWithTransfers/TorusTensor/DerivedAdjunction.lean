/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ProjectiveComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives
import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Derived Hom for torus tensor on projective transfer presheaves

Apply the actual torus tensor to bounded-above projective presheaf
representatives and then sheafify. The right side forgets the sheaf
condition on K-injective complexes and applies exact presheaf reindexing.
The homotopy adjunction on these representatives gives the natural
derived Hom equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w₁ w₂

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers
open Stacks.Injectives.KInjectiveResolution

/-- The transfer presheaf category in the coefficient universe of the native projective model. -/
abbrev LargePresheaves (k : Type u) [Field k] := PresheafWithTransfers.{u + 1} k

/-- The transfer sheaf category in the same coefficient universe. -/
abbrev LargeSheaves (k : Type u) [Field k] := SheafWithTransfers.{u + 1} k

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
variable [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "c" => ComplexShape.up ℤ
local notation "L" => parameterTensorFunctor Gₘ ⋙ nisnevichSheafify k
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "R" => U ⋙ T

/-- Apply the literal underlying-presheaf functor and then localize. -/
abbrev forgetComplexToDerived : CochainComplex NST ℤ ⥤ DerivedCategory PST :=
  (U).mapHomologicalComplex c ⋙ DerivedCategory.Q

instance : (forgetComplexToDerived k).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso NST c) :=
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q U

/-- The actual right-derived underlying transfer presheaf of a transfer sheaf complex. -/
@[no_expose]
def forgetDerivedFunctor : DerivedCategory NST ⥤ DerivedCategory PST :=
  (forgetComplexToDerived k).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso NST c)

/-- The comparison from forgetting the original complex to its derived value. -/
@[no_expose]
def forgetDerivedUnit : forgetComplexToDerived k ⟶ DerivedCategory.Q ⋙ forgetDerivedFunctor k :=
  (forgetComplexToDerived k).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso NST c)

instance : (forgetDerivedFunctor k).IsRightDerivedFunctor (forgetDerivedUnit k)
    (HomologicalComplex.quasiIso NST c) := by
  dsimp only [forgetDerivedFunctor, forgetDerivedUnit]
  infer_instance

/-- Derived forget followed by exact reindexing by the original torus. -/
abbrev torusTensorDerivedRight : DerivedCategory NST ⥤ DerivedCategory PST :=
  forgetDerivedFunctor k ⋙ (T).mapDerivedCategory

/-- The native homotopy category restricted to K-injective transfer sheaf complexes. -/
abbrev TorusTensorInjectiveHomotopy :=
  ObjectProperty.FullSubcategory
    (fun I : HomotopyCategory NST c => CochainComplex.IsKInjective I.as)

/-- The inclusion of the original K-injective complexes into the homotopy category. -/
abbrev torusTensorInjectiveInclusion :
    TorusTensorInjectiveHomotopy k ⥤ HomotopyCategory NST c :=
  ObjectProperty.ι _

/-- The native derived quotient on the original K-injective complexes. -/
abbrev torusTensorInjectiveToDerived : TorusTensorInjectiveHomotopy k ⥤ DerivedCategory NST :=
  torusTensorInjectiveInclusion k ⋙ DerivedCategory.Qh

omit [HasDerivedCategory PST] in
private theorem torusTensorInjectiveToDerived_map_bijective (I J : TorusTensorInjectiveHomotopy k) :
    Function.Bijective ((torusTensorInjectiveToDerived k).map : (I ⟶ J) → _) := by
  let : CochainComplex.IsKInjective J.obj.as :=
    J.property
  exact (CochainComplex.IsKInjective.Qh_map_bijective I.obj J.obj.as).comp
    (Functor.FullyFaithful.ofFullyFaithful (torusTensorInjectiveInclusion k)).homEquiv.bijective

instance : (torusTensorInjectiveToDerived k).Full where
  map_surjective := (torusTensorInjectiveToDerived_map_bijective k _ _).2

instance : (torusTensorInjectiveToDerived k).Faithful where
  map_injective h := (torusTensorInjectiveToDerived_map_bijective k _ _).1 h

instance : (torusTensorInjectiveToDerived k).EssSurj where
  mem_essImage K := by
    have := Localization.essSurj (DerivedCategory.Q (C := NST))
      (HomologicalComplex.quasiIso NST c)
    obtain ⟨J, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := NST)) K
    obtain ⟨I, f, hI, hf⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck J
    let : QuasiIso f := hf
    refine ⟨⟨(HomotopyCategory.quotient NST c).obj I, ?_⟩, ⟨?_⟩⟩
    · exact hI
    · exact (DerivedCategory.quotientCompQhIso NST).app I ≪≫
        (asIso (DerivedCategory.Q.map f)).symm ≪≫ e

instance : (torusTensorInjectiveToDerived k).IsEquivalence where

/-- The inclusion of the original bounded-above projective homotopy category. -/
abbrev projInclusion :
    BoundedAboveProjectiveHomotopy k ⥤ HomotopyCategory PST c :=
  (boundedAboveProjectiveCondition k).ι

/-- The literal torus tensor and exact sheafification on projective representatives. -/
abbrev projectiveTensorModel :
    BoundedAboveProjectiveHomotopy k ⥤ DerivedCategory NST :=
  projectiveHomotopyMapToDerivedMinus k (parameterTensorFunctor Gₘ) ⋙
    (nisnevichSheafify k).mapDerivedCategoryMinus ⋙ DerivedCategory.Minus.ι

/-- The projective tensor model is obtained from the literal homotopy tensor. -/
def projectiveTensorModelIso :
    projectiveTensorModel k ≅ projInclusion k ⋙ (L).mapHomotopyCategory c ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerLeft (projInclusion k ⋙ (parameterTensorFunctor Gₘ).mapHomotopyCategory c)
    (nisnevichSheafify k).mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerLeft (projInclusion k)
        (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl L) c)
          DerivedCategory.Qh)

/-- The derived-forget unit transported to the actual homotopy quotient. -/
def forgetHomotopyUnit :
    (U).mapHomotopyCategory c ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ forgetDerivedFunctor k :=
  Stacks.Injectives.homotopyUnitOfComplexUnit U (forgetDerivedFunctor k) (forgetDerivedUnit k)

/-- On K-injective complexes, derived forget and torus reindexing are computed termwise. -/
def torusTensorInjectiveReindexingIso :
    torusTensorInjectiveInclusion k ⋙ (R).mapHomotopyCategory c ⋙ DerivedCategory.Qh ≅
      torusTensorInjectiveToDerived k ⋙ torusTensorDerivedRight k := by
  let α := Functor.whiskerLeft (torusTensorInjectiveInclusion k) (forgetHomotopyUnit k)
  let : IsIso α := (NatTrans.isIso_iff_isIso_app α).2 (fun I =>
    Stacks.Injectives.isIso_homotopyUnitOfComplexUnit_app_quotient U
      (forgetDerivedFunctor k) (forgetDerivedUnit k) I.obj.as
      (I.property))
  exact Functor.isoWhiskerLeft (torusTensorInjectiveInclusion k)
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl R) c).symm
        DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft (torusTensorInjectiveInclusion k ⋙ (U).mapHomotopyCategory c)
      (T).mapDerivedCategoryFactorsh.symm ≪≫
    Functor.isoWhiskerRight (asIso α) (T).mapDerivedCategory

/-- The original cochain adjunction after passing to homotopy classes. -/
def torusTensorHomotopyAdjunction :
    (L).mapHomotopyCategory c ⊣ (R).mapHomotopyCategory c :=
  ((parameterTensorAdjunction Gₘ).comp
    (nisnevichSheafificationAdjunction k)).mapHomotopyCategoryAdjunction c

/-- The original tensor and sections adjunction applied to cochain complexes. -/
def torusTensorCochainAdjunction :
    (L).mapHomologicalComplex c ⊣ (R).mapHomologicalComplex c :=
  ((parameterTensorAdjunction Gₘ).comp
    (nisnevichSheafificationAdjunction k)).mapHomologicalComplexAdjunction c

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
/-- Forgetting the sheaf condition sends K-injectives to K-injectives by
exactness of the actual left adjoint, Nisnevich sheafification. -/
theorem isKInjective_forget_mapHomologicalComplex (I : CochainComplex NST ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((U).mapHomologicalComplex c).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact U (nisnevichSheafify k)
    (nisnevichSheafificationAdjunction k) I

private abbrev Proj := BoundedAboveProjectiveHomotopy k

private abbrev leftHomotopy (P : Proj k) : HomotopyCategory NST c :=
  ((L).mapHomotopyCategory c).obj P.obj

private abbrev rightHomotopy (I : TorusTensorInjectiveHomotopy k) : HomotopyCategory PST c :=
  ((R).mapHomotopyCategory c).obj I.obj

private abbrev leftModel (P : Proj k) : DerivedCategory NST :=
  DerivedCategory.Qh.obj (leftHomotopy k P)

private abbrev sourceModel (P : Proj k) : DerivedCategory PST := DerivedCategory.Qh.obj P.obj

/-- The localized Hom transpose on the actual projective and K-injective representatives. -/
@[no_expose]
def torusTensorHomEquivOnRepresentatives (P : BoundedAboveProjectiveHomotopy k)
    (I : TorusTensorInjectiveHomotopy k) :
    (DerivedCategory.Qh.obj (((L).mapHomotopyCategory c).obj P.obj) ⟶
      (torusTensorInjectiveToDerived k).obj I) ≃
      (DerivedCategory.Qh.obj P.obj ⟶
        (torusTensorDerivedRight k).obj ((torusTensorInjectiveToDerived k).obj I)) := by
  let : CochainComplex.IsKInjective I.obj.as :=
    I.property
  let n := P.property.choose
  have ⟨hn, hP⟩ := P.property.choose_spec
  let : CochainComplex.IsStrictlyLE P.obj.as n := hn
  let : ∀ i : ℤ, Projective (P.obj.as.X i) := hP
  let : CochainComplex.IsKProjective P.obj.as :=
    CochainComplex.isKProjective_of_projective P.obj.as n
  let e₁ := Equiv.ofBijective (DerivedCategory.Qh.map : (leftHomotopy k P ⟶ I.obj) → _)
    (CochainComplex.IsKInjective.Qh_map_bijective (leftHomotopy k P) I.obj.as)
  let e₂ := (torusTensorHomotopyAdjunction k).homEquiv P.obj I.obj
  let e₃ := Equiv.ofBijective (DerivedCategory.Qh.map : (P.obj ⟶ rightHomotopy k I) → _)
    (CochainComplex.IsKProjective.Qh_map_bijective P.obj.as (rightHomotopy k I))
  let e₄ := Iso.homCongr (Iso.refl (sourceModel k P)) ((torusTensorInjectiveReindexingIso k).app I)
  exact e₁.symm.trans (e₂.trans (e₃.trans e₄))

/-- The representative Hom equivalence transposes the original homotopy class. -/
theorem tensorHomOnRepresentatives_map (P : BoundedAboveProjectiveHomotopy k)
    (I : TorusTensorInjectiveHomotopy k)
    (f : ((L).mapHomotopyCategory c).obj P.obj ⟶ I.obj) :
    torusTensorHomEquivOnRepresentatives k P I (DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map ((torusTensorHomotopyAdjunction k).homEquiv P.obj I.obj f) ≫
        (torusTensorInjectiveReindexingIso k).hom.app I := by
  let : CochainComplex.IsKInjective I.obj.as :=
    I.property
  let e := Equiv.ofBijective (DerivedCategory.Qh.map : (leftHomotopy k P ⟶ I.obj) → _)
    (CochainComplex.IsKInjective.Qh_map_bijective (leftHomotopy k P) I.obj.as)
  change 𝟙 _ ≫ DerivedCategory.Qh.map
      ((torusTensorHomotopyAdjunction k).homEquiv P.obj I.obj (e.symm (e f))) ≫ _ = _
  rw [Equiv.symm_apply_apply, Category.id_comp]
  rfl

/-- The original representative transpose is natural in a morphism of
bounded-above projective complexes. -/
theorem torusTensorHomEquivOnRepresentatives_precompose
    {P P' : BoundedAboveProjectiveHomotopy k} (I : TorusTensorInjectiveHomotopy k)
    (f : P' ⟶ P) (g : ((L).mapHomotopyCategory c ⋙ DerivedCategory.Qh).obj P.obj ⟶
      (torusTensorInjectiveToDerived k).obj I) :
    torusTensorHomEquivOnRepresentatives k P' I
        (DerivedCategory.Qh.map (((L).mapHomotopyCategory c).map f.hom) ≫ g) =
      DerivedCategory.Qh.map f.hom ≫ torusTensorHomEquivOnRepresentatives k P I g := by
  let : CochainComplex.IsKInjective I.obj.as := I.property
  obtain ⟨g₀, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (leftHomotopy k P) I.obj.as).2 g
  let D := DerivedCategory.Qh (C := NST)
  let f₀ := ((L).mapHomotopyCategory c).map f.hom
  have h : D.map f₀ ≫ D.map g₀ = D.map (f₀ ≫ g₀) := (D.map_comp f₀ g₀).symm
  change torusTensorHomEquivOnRepresentatives k P' I (D.map f₀ ≫ D.map g₀) = _
  rw [h]
  rw [tensorHomOnRepresentatives_map, tensorHomOnRepresentatives_map,
    Adjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]

/-- The representative transpose is additive on the original localized Hom groups. -/
theorem torusTensorHomEquivOnRepresentatives_sub (P : BoundedAboveProjectiveHomotopy k)
    (I : TorusTensorInjectiveHomotopy k)
    (f g : ((L).mapHomotopyCategory c ⋙ DerivedCategory.Qh).obj P.obj ⟶
      (torusTensorInjectiveToDerived k).obj I) :
    torusTensorHomEquivOnRepresentatives k P I (f - g) =
      torusTensorHomEquivOnRepresentatives k P I f -
        torusTensorHomEquivOnRepresentatives k P I g := by
  let : CochainComplex.IsKInjective I.obj.as := I.property
  let F := ((L).mapHomotopyCategory c).obj P.obj
  let Q := DerivedCategory.Qh (C := NST)
  obtain ⟨f₀, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective F I.obj.as).2 f
  obtain ⟨g₀, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective F I.obj.as).2 g
  change torusTensorHomEquivOnRepresentatives k P I (Q.map f₀ - Q.map g₀) = _
  calc
    _ = torusTensorHomEquivOnRepresentatives k P I (Q.map (f₀ - g₀)) :=
      congrArg (torusTensorHomEquivOnRepresentatives k P I)
        (Q.map_sub (f := f₀) (g := g₀)).symm
    _ = _ := by
      rw [tensorHomOnRepresentatives_map k P I (f₀ - g₀), tensorHomOnRepresentatives_map k P I f₀,
        tensorHomOnRepresentatives_map k P I g₀, Adjunction.homAddEquiv_sub,
        Functor.map_sub, Preadditive.sub_comp]

private def modelHomEquiv (P : Proj k) (I : TorusTensorInjectiveHomotopy k) :
    ((projectiveTensorModel k).obj P ⟶ (torusTensorInjectiveToDerived k).obj I) ≃
      (sourceModel k P ⟶
        (torusTensorDerivedRight k).obj ((torusTensorInjectiveToDerived k).obj I)) :=
  (Iso.homCongr ((projectiveTensorModelIso k).app P) (Iso.refl _)).trans
    (torusTensorHomEquivOnRepresentatives k P I)

private theorem modelHomEquiv_apply (P : Proj k) (I : TorusTensorInjectiveHomotopy k)
    (f : (projectiveTensorModel k).obj P ⟶ (torusTensorInjectiveToDerived k).obj I) :
    modelHomEquiv k P I f =
      torusTensorHomEquivOnRepresentatives k P I ((projectiveTensorModelIso k).inv.app P ≫ f) := by
  simp only [modelHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rfl

private theorem modelHomEquiv_precompose {P P' : Proj k} (I : TorusTensorInjectiveHomotopy k)
    (f : P' ⟶ P) (a : (projectiveTensorModel k).obj P ⟶ (torusTensorInjectiveToDerived k).obj I) :
    modelHomEquiv k P' I ((projectiveTensorModel k).map f ≫ a) =
      DerivedCategory.Qh.map f.hom ≫ modelHomEquiv k P I a := by
  let e := projectiveTensorModelIso k
  have he : e.inv.app P' ≫ (projectiveTensorModel k).map f ≫ a =
      DerivedCategory.Qh.map (((L).mapHomotopyCategory c).map f.hom) ≫ e.inv.app P ≫ a := by
    exact (e.inv.naturality_assoc f a).symm
  simp only [modelHomEquiv_apply]
  change torusTensorHomEquivOnRepresentatives k P' I (e.inv.app P' ≫ _ ≫ _) =
    DerivedCategory.Qh.map f.hom ≫ torusTensorHomEquivOnRepresentatives k P I (e.inv.app P ≫ a)
  rw [he]
  exact torusTensorHomEquivOnRepresentatives_precompose k I f (e.inv.app P ≫ a)

private theorem modelHomEquiv_postcompose (P : Proj k) {I I' : TorusTensorInjectiveHomotopy k}
    (f : I ⟶ I') (a : (projectiveTensorModel k).obj P ⟶ (torusTensorInjectiveToDerived k).obj I) :
    modelHomEquiv k P I' (a ≫ (torusTensorInjectiveToDerived k).map f) =
      modelHomEquiv k P I a ≫
        (torusTensorDerivedRight k).map ((torusTensorInjectiveToDerived k).map f) := by
  let e := projectiveTensorModelIso k
  let : CochainComplex.IsKInjective I.obj.as :=
    I.property
  obtain ⟨b, hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (leftHomotopy k P) I.obj.as).2
    (e.inv.app P ≫ a)
  simp only [modelHomEquiv_apply]
  change torusTensorHomEquivOnRepresentatives k P I' (e.inv.app P ≫ a ≫ _) =
    torusTensorHomEquivOnRepresentatives k P I (e.inv.app P ≫ a) ≫ _
  have hleft : e.inv.app P ≫ a ≫ (torusTensorInjectiveToDerived k).map f =
      DerivedCategory.Qh.map (b ≫ f.hom) := by
    rw [← Category.assoc, ← hb]
    exact (DerivedCategory.Qh.map_comp b f.hom).symm
  rw [hleft, ← hb]
  simp only [tensorHomOnRepresentatives_map]
  rw [Adjunction.homEquiv_naturality_right, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (DerivedCategory.Qh.map
    ((torusTensorHomotopyAdjunction k).homEquiv P.obj I.obj b) ≫ ·)
      ((torusTensorInjectiveReindexingIso k).hom.naturality f)

private abbrev projectiveRepresentative :
    DerivedCategory.Minus PST ⥤ Proj k :=
  (boundedAboveProjectiveEquivalence k).inverse

private abbrev injectiveRepresentative : DerivedCategory NST ⥤ TorusTensorInjectiveHomotopy k :=
  (torusTensorInjectiveToDerived k).asEquivalence.inverse

private def projectiveRepresentativeIso :
    projectiveRepresentative k ⋙ projectiveHomotopyToDerivedMinus k ⋙
      DerivedCategory.Minus.ι ≅ DerivedCategory.Minus.ι (C := PST) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedAboveProjectiveEquivalence k).counitIso
      DerivedCategory.Minus.ι ≪≫ Functor.leftUnitor _

private def injectiveRepresentativeIso :
    injectiveRepresentative k ⋙ torusTensorInjectiveToDerived k ≅ 𝟭 (DerivedCategory NST) :=
  (torusTensorInjectiveToDerived k).asEquivalence.counitIso

local notation "LD" => projectiveTorusTensorToDerivedMinus k ⋙ DerivedCategory.Minus.ι
local notation "RD" => torusTensorDerivedRight k

/-- Derived Hom from the projective torus tensor into any transfer sheaf
complex is derived Hom into the exact torus reindexing of its derived
underlying presheaf. The source of the tensor is bounded above. -/
@[no_expose]
def projectiveTorusTensorDerivedHomEquiv
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) :
    ((LD).obj P ⟶ K) ≃ (P.obj ⟶ (RD).obj K) :=
  let E := projectiveRepresentative k
  let J := injectiveRepresentative k
  let e := (injectiveRepresentativeIso k).app K
  let d := (projectiveRepresentativeIso k).app P
  (Iso.homCongr (Iso.refl _) e.symm).trans
    ((modelHomEquiv k (E.obj P) (J.obj K)).trans (Iso.homCongr d ((RD).mapIso e)))

/-- The derived Hom equivalence takes precomposition to the original
derived presheaf map. -/
theorem projectiveTorusTensorDerivedHomEquiv_precompose
    {P P' : DerivedCategory.Minus PST} (K : DerivedCategory NST)
    (f : P' ⟶ P) (g : (LD).obj P ⟶ K) :
    projectiveTorusTensorDerivedHomEquiv k P' K ((LD).map f ≫ g) =
      f.hom ≫ projectiveTorusTensorDerivedHomEquiv k P K g := by
  let E := projectiveRepresentative k
  let I := (injectiveRepresentative k).obj K
  let e := (injectiveRepresentativeIso k).app K
  let d := projectiveRepresentativeIso k
  let F := projectiveTensorModel k
  let r := (RD).map e.hom
  change d.inv.app P' ≫
      modelHomEquiv k (E.obj P') I (𝟙 _ ≫ (F.map (E.map f) ≫ g) ≫ e.inv) ≫ r =
    f.hom ≫ d.inv.app P ≫ modelHomEquiv k (E.obj P) I (𝟙 _ ≫ g ≫ e.inv) ≫ r
  simp only [Category.id_comp, Category.assoc]
  have hm := modelHomEquiv_precompose k I (E.map f) (g ≫ e.inv)
  change d.inv.app P' ≫ modelHomEquiv k (E.obj P') I (F.map (E.map f) ≫ g ≫ e.inv) ≫ r =
    f.hom ≫ d.inv.app P ≫ modelHomEquiv k (E.obj P) I (g ≫ e.inv) ≫ r
  rw [hm]
  have hd : d.inv.app P' ≫ DerivedCategory.Qh.map (E.map f).hom = f.hom ≫ d.inv.app P :=
    (d.inv.naturality f).symm
  let a := modelHomEquiv k (E.obj P) I (g ≫ e.inv)
  calc
    _ = (d.inv.app P' ≫ DerivedCategory.Qh.map (E.map f).hom) ≫ a ≫ r := by
      simp only [Category.assoc]
      rfl
    _ = (f.hom ≫ d.inv.app P) ≫ a ≫ r := congrArg (· ≫ a ≫ r) hd
    _ = _ := Category.assoc _ _ _

/-- The derived Hom equivalence carries postcomposition to the actual
derived reindexing map on the target. -/
theorem projectiveTorusTensorDerivedHomEquiv_postcompose
    (P : DerivedCategory.Minus PST) {K K' : DerivedCategory NST}
    (f : (LD).obj P ⟶ K) (g : K ⟶ K') :
    projectiveTorusTensorDerivedHomEquiv k P K' (f ≫ g) =
      projectiveTorusTensorDerivedHomEquiv k P K f ≫ (RD).map g := by
  let E := (projectiveRepresentative k).obj P
  let J := injectiveRepresentative k
  let e := injectiveRepresentativeIso k
  let d := (projectiveRepresentativeIso k).app P
  have he : g ≫ e.inv.app K' = e.inv.app K ≫ (torusTensorInjectiveToDerived k).map (J.map g) :=
    e.inv.naturality g
  have hmap : (RD).map ((torusTensorInjectiveToDerived k).map (J.map g)) ≫ (RD).map (e.hom.app K') =
      (RD).map (e.hom.app K) ≫ (RD).map g :=
    ((RD).map_comp _ _).symm.trans
      ((congrArg (RD).map (e.hom.naturality g)).trans ((RD).map_comp _ _))
  change d.inv ≫ modelHomEquiv k E (J.obj K') (𝟙 _ ≫ (f ≫ g) ≫ e.inv.app K') ≫
      (RD).map (e.hom.app K') =
    (d.inv ≫ modelHomEquiv k E (J.obj K) (𝟙 _ ≫ f ≫ e.inv.app K) ≫
      (RD).map (e.hom.app K)) ≫ (RD).map g
  simp only [Category.id_comp, Category.assoc, he]
  rw [← Category.assoc f (e.inv.app K), modelHomEquiv_postcompose]
  simp only [Category.assoc]
  rw [hmap]

/-- The chosen projective representative and any original K-injective target
give the same transpose as the derived Hom equivalence. -/
theorem projectiveTorusTensorDerivedHomEquiv_on_representatives
    (P : DerivedCategory.Minus PST) (I : TorusTensorInjectiveHomotopy k)
    (f : (LD).obj P ⟶ (torusTensorInjectiveToDerived k).obj I) :
    let E := (boundedAboveProjectiveEquivalence k).inverse.obj P
    let d := (DerivedCategory.Minus.ι (C := PST)).mapIso
      ((boundedAboveProjectiveEquivalence k).counitIso.app P)
    projectiveTorusTensorDerivedHomEquiv k P ((torusTensorInjectiveToDerived k).obj I) f =
      d.inv ≫ torusTensorHomEquivOnRepresentatives k E I
        ((projectiveTensorModelIso k).inv.app E ≫ f) := by
  intro E d
  let J := injectiveRepresentative k
  let q := torusTensorInjectiveToDerived k
  let K := q.obj I
  let e := (injectiveRepresentativeIso k).app K
  let f' := q.preimage e.inv
  have hf' : q.map f' = e.inv := q.map_preimage e.inv
  have he : (RD).map (q.map f') ≫ (RD).map e.hom = 𝟙 _ := by
    rw [← (RD).map_comp, hf', e.inv_hom_id]
    exact (RD).map_id K
  change (projectiveRepresentativeIso k).inv.app P ≫
      modelHomEquiv k E (J.obj K) (𝟙 _ ≫ f ≫ e.inv) ≫ (RD).map e.hom = _
  rw [Category.id_comp, ← hf', modelHomEquiv_postcompose, Category.assoc, he, Category.comp_id,
    modelHomEquiv_apply]
  have hd : (projectiveRepresentativeIso k).inv.app P = d.inv := by
    unfold projectiveRepresentativeIso
    simp only [Iso.trans_inv, Functor.leftUnitor_inv_app, Iso.symm_inv, Functor.associator_hom_app,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Category.assoc, Category.id_comp, Category.comp_id]
    rfl
  exact congrArg (· ≫ torusTensorHomEquivOnRepresentatives k E I
    ((projectiveTensorModelIso k).inv.app E ≫ f)) hd

/-- The derived Hom equivalence preserves subtraction of the actual morphisms. -/
theorem projectiveTorusTensorDerivedHomEquiv_sub
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST)
    (f g : (LD).obj P ⟶ K) :
    projectiveTorusTensorDerivedHomEquiv k P K (f - g) =
      projectiveTorusTensorDerivedHomEquiv k P K f -
        projectiveTorusTensorDerivedHomEquiv k P K g := by
  let E := (projectiveRepresentative k).obj P
  let J := (injectiveRepresentative k).obj K
  let e := (injectiveRepresentativeIso k).app K
  let d := (projectiveRepresentativeIso k).app P
  let a := (projectiveTensorModelIso k).inv.app E
  let H := torusTensorHomEquivOnRepresentatives k E J
  let t := (RD).map e.hom
  have h (x : (LD).obj P ⟶ K) :
      projectiveTorusTensorDerivedHomEquiv k P K x = d.inv ≫ H (a ≫ x ≫ e.inv) ≫ t := by
    change d.inv ≫ modelHomEquiv k E J (𝟙 _ ≫ x ≫ e.inv) ≫ t = _
    simp only [Category.id_comp, modelHomEquiv_apply, H, a]
  simp only [h]
  have hfg : a ≫ (f - g) ≫ e.inv = (a ≫ f ≫ e.inv) - (a ≫ g ≫ e.inv) := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
  change d.inv ≫ torusTensorHomEquivOnRepresentatives k E J (a ≫ (f - g) ≫ e.inv) ≫ t =
    _ - _
  rw [hfg, torusTensorHomEquivOnRepresentatives_sub]
  simp only [H, Preadditive.sub_comp, Preadditive.comp_sub]

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
/-- The homotopy transpose of a cochain map is the class of its cochain transpose. -/
theorem torusTensorHomotopyAdjunction_homEquiv_quotient
    {P : CochainComplex PST ℤ} {I : CochainComplex NST ℤ}
    (f : ((L).mapHomologicalComplex c).obj P ⟶ I) :
    (torusTensorHomotopyAdjunction k).homEquiv
      ((HomotopyCategory.quotient PST c).obj P) ((HomotopyCategory.quotient NST c).obj I)
      ((HomotopyCategory.quotient NST c).map f) =
    (HomotopyCategory.quotient PST c).map ((torusTensorCochainAdjunction k).homEquiv P I f) := by
  let adj := (parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (HomotopyCategory.quotient PST c).map
      ((adj.mapHomologicalComplexAdjunction c).unit.app P) ≫
    (HomotopyCategory.quotient PST c).map (((R).mapHomologicalComplex c).map f) = _
  exact ((HomotopyCategory.quotient PST c).map_comp _ _).symm

/-- On a projective source and K-injective target, the equivalence
localizes the transpose from the actual cochain adjunction. -/
theorem projectiveTorusTensor_homotopyHomEquiv_map
    (P : BoundedAboveProjectiveHomotopy k) (I : CochainComplex NST ℤ)
    [hI : CochainComplex.IsKInjective I]
    (f : ((L).mapHomologicalComplex c).obj P.obj.as ⟶ I) :
    let J : TorusTensorInjectiveHomotopy k :=
      ⟨(HomotopyCategory.quotient NST c).obj I, hI⟩
    torusTensorHomEquivOnRepresentatives k P J
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient NST c).map f)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient PST c).map
      ((torusTensorCochainAdjunction k).homEquiv P.obj.as I f)) ≫
      (torusTensorInjectiveReindexingIso k).hom.app J := by
  intro J
  rw [tensorHomOnRepresentatives_map]
  exact congrArg
    (fun g => DerivedCategory.Qh.map g ≫ (torusTensorInjectiveReindexingIso k).hom.app J)
    (torusTensorHomotopyAdjunction_homEquiv_quotient k f)

end AlgebraicGeometry.SheafWithTransfers
