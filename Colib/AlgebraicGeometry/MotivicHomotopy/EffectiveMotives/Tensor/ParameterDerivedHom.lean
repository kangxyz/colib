/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardExactness
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# Derived Hom for a represented parameter

The pushforward coend preserves projectives because its right adjoint is
exact. Both sides of the original homotopy adjunction can therefore be
computed on a bounded-above projective representative and an arbitrary
target in the derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafWithTransfers (LargePresheaves)

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  (F : Cor k ⥤ Cor k) [F.Additive]

local notation "PST(" K ")" => LargePresheaves K
local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "Q(" K ")" => DerivedCategory.Qh (C := PST(K))
local notation "L(" F ")" => coendPushforward F
local notation "R(" F ")" => additivePrecompose F
set_option quotPrecheck false in
local notation "L₀(" F ")" => (L(F)).mapHomotopyCategory c
set_option quotPrecheck false in
local notation "R₀(" F ")" => (R(F)).mapHomotopyCategory c
local notation "E(" K ")" => boundedAboveProjectiveEquivalence K

/-- The actual projective derived parameter tensor on bounded-above presheaves. -/
abbrev derivedParameterPushforward : DerivedCategory.Minus PST(k) ⥤ DerivedCategory.Minus PST(k) :=
  projectiveDerivedMinusFunctor k L(F)

omit [HasDerivedCategory PST(k)] in
private theorem projectiveRepresentative_isKProjective
    (J : BoundedAboveProjectiveHomotopy k) : CochainComplex.IsKProjective J.obj.as := by
  obtain ⟨b, hb, hp⟩ := J.property
  let : CochainComplex.IsStrictlyLE J.obj.as b := hb
  let : ∀ i, Projective (J.obj.as.X i) := hp
  exact CochainComplex.isKProjective_of_projective J.obj.as b

omit [HasDerivedCategory PST(k)] in
private theorem pushforwardRepresentative_isKProjective
    (J : BoundedAboveProjectiveHomotopy k) :
    CochainComplex.IsKProjective ((L₀(F)).obj J.obj).as := by
  obtain ⟨b, hb, hp⟩ := J.property
  let : CochainComplex.IsStrictlyLE J.obj.as b := hb
  let I : CochainComplex PST(k) ℤ := ((L(F)).mapHomologicalComplex c).obj J.obj.as
  change CochainComplex.IsKProjective I
  let : I.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff I b).2
    (fun i hi => (L(F)).map_isZero (CochainComplex.isZero_of_isStrictlyLE J.obj.as b i hi))
  let : ∀ i, Projective (I.X i) := fun i =>
    have : Projective (J.obj.as.X i) := hp i
    inferInstanceAs (Projective ((L(F)).obj (J.obj.as.X i)))
  exact CochainComplex.isKProjective_of_projective I b

private def homEquivOnProjectives (J : BoundedAboveProjectiveHomotopy k)
    (V : HomotopyCategory PST(k) c) :
    ((Q(k)).obj ((L₀(F)).obj J.obj) ⟶ (Q(k)).obj V) ≃
      ((Q(k)).obj J.obj ⟶ (R(F)).mapDerivedCategory.obj ((Q(k)).obj V)) :=
  letI : CochainComplex.IsKProjective ((L₀(F)).obj J.obj).as :=
    pushforwardRepresentative_isKProjective F J
  letI : CochainComplex.IsKProjective J.obj.as := projectiveRepresentative_isKProjective J
  (Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective
    ((L₀(F)).obj J.obj).as V)).symm.trans
      (((coendPushforwardAdjunction F).mapHomotopyCategoryAdjunction c).homEquiv J.obj V |>.trans
        ((Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective J.obj.as
          ((R₀(F)).obj V))).trans ((R(F)).mapDerivedCategoryFactorsh.app V).symm.homToEquiv))

private theorem homEquivOnProjectives_map (J : BoundedAboveProjectiveHomotopy k)
    (V : HomotopyCategory PST(k) c) (g : (L₀(F)).obj J.obj ⟶ V) :
    homEquivOnProjectives F J V ((Q(k)).map g) =
      (Q(k)).map
        (((coendPushforwardAdjunction F).mapHomotopyCategoryAdjunction c).homEquiv J.obj V g) ≫
        (R(F)).mapDerivedCategoryFactorsh.inv.app V := by
  let : CochainComplex.IsKProjective ((L₀(F)).obj J.obj).as :=
    pushforwardRepresentative_isKProjective F J
  let e := Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective
    ((L₀(F)).obj J.obj).as V)
  let H := (coendPushforwardAdjunction F).mapHomotopyCategoryAdjunction c
  change (Q(k)).map (H.homEquiv J.obj V (e.symm (e g))) ≫ _ = _
  rw [e.symm_apply_apply]
  rfl

/-- The actual represented coend pushforward on bounded-above complexes
transposes to exact precomposition on unbounded derived presheaves. -/
@[no_expose]
def derivedParameterPushforwardHomEquiv
    (P : DerivedCategory.Minus PST(k)) (K : DerivedCategory PST(k)) :
    (((derivedParameterPushforward F).obj P).obj ⟶ K) ≃
      (P.obj ⟶ (R(F)).mapDerivedCategory.obj K) :=
  let J := (E(k)).inverse.obj P
  let V := (Q(k)).objPreimage K
  let a := (Q(k)).objObjPreimageIso K
  let b := (DerivedCategory.Minus.ι (C := PST(k))).mapIso ((E(k)).counitIso.app P)
  a.symm.homToEquiv.trans ((homEquivOnProjectives F J V).trans
    (b.homCongr ((R(F)).mapDerivedCategory.mapIso a)))

/-- Precomposition in the derived Hom equivalence is the original
bounded-above derived morphism. -/
theorem derivedParameterPushforwardHomEquiv_precompose
    {P P' : DerivedCategory.Minus PST(k)} (K : DerivedCategory PST(k)) (f : P' ⟶ P)
    (g : ((derivedParameterPushforward F).obj P).obj ⟶ K) :
    derivedParameterPushforwardHomEquiv F P' K (((derivedParameterPushforward F).map f).hom ≫ g) =
      f.hom ≫ derivedParameterPushforwardHomEquiv F P K g := by
  let J := (E(k)).inverse.obj P
  let J' := (E(k)).inverse.obj P'
  let m := ((E(k)).inverse.map f).hom
  let V := (Q(k)).objPreimage K
  let a := (Q(k)).objObjPreimageIso K
  let b := (DerivedCategory.Minus.ι (C := PST(k))).mapIso ((E(k)).counitIso.app P)
  let b' := (DerivedCategory.Minus.ι (C := PST(k))).mapIso ((E(k)).counitIso.app P')
  let H := (coendPushforwardAdjunction F).mapHomotopyCategoryAdjunction c
  let : CochainComplex.IsKProjective ((L₀(F)).obj J.obj).as :=
    pushforwardRepresentative_isKProjective F J
  obtain ⟨v, hv⟩ := (CochainComplex.IsKProjective.Qh_map_bijective ((L₀(F)).obj J.obj).as V).2
    (g ≫ a.inv)
  have h₀ : (Q(k)).map ((L₀(F)).map m) ≫ g ≫ a.inv = (Q(k)).map ((L₀(F)).map m ≫ v) := by
    rw [← hv, Functor.map_comp]
  have h₁ : b'.inv ≫ (Q(k)).map m = f.hom ≫ b.inv := by
    exact congrArg (fun h => h.hom) (((E(k)).counitIso.inv.naturality f).symm)
  change b'.inv ≫ (homEquivOnProjectives F J' V (((Q(k)).map ((L₀(F)).map m) ≫ g) ≫ a.inv) ≫
      (R(F)).mapDerivedCategory.map a.hom) =
    f.hom ≫ b.inv ≫ (homEquivOnProjectives F J V (g ≫ a.inv) ≫
      (R(F)).mapDerivedCategory.map a.hom)
  have h₂ : homEquivOnProjectives F J' V ((Q(k)).map ((L₀(F)).map m ≫ v)) =
      (Q(k)).map m ≫ homEquivOnProjectives F J V ((Q(k)).map v) := by
    rw [homEquivOnProjectives_map, homEquivOnProjectives_map,
      H.homEquiv_naturality_left, (Q(k)).map_comp, Category.assoc]
  rw [Category.assoc ((Q(k)).map ((L₀(F)).map m)) g a.inv, h₀, ← hv, h₂]
  simp only [Category.assoc, reassoc_of% h₁]

end AlgebraicGeometry.PresheafWithTransfers
