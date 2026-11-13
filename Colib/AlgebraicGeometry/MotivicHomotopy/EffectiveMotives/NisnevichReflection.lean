/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichLift
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingularPresheafReflection
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.DerivedForgetInvariance
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology

/-!
# Bounded-above effective Nisnevich reflection

For a bounded-above source, maps to the derived underlying presheaf of
an effective object factor through the good upper truncation at the
source bound. Strict A¹-invariance makes the truncated target local
for the original singular augmentation. The counit of exact
sheafification realizes every bounded-above Nisnevich object in this way.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => SheafWithTransfers.LargePresheaves k
local notation "NST" => SheafWithTransfers.LargeSheaves k
local notation "a" => nisnevichSheafify k
local notation "U" => SheafWithTransfers.forgetDerivedFunctor k
local notation "Sing" => singularPresheafDerivedFunctor k
local notation "η" => singularPresheafDerivedUnit k

/-- Sheafify the original bounded-above singular total complex. -/
@[expose]
def singularPresheafToEffective : DerivedCategory.Minus PST ⥤ EffectiveMotivesMinus k :=
  (effectiveCohomologyCondition k).lift (Sing ⋙ derivedNisnevichSheafification k) (fun P i => by
    let K := ((Sing).obj P).obj
    let e := ((a).mapDerivedCategoryHomologyIso i).app K
    exact IsA1Invariant.of_iso (nisnevichSheafify_isA1Invariant _
      (singularPresheafDerivedFunctor_cohomology_isA1Invariant k P i))
        ((SheafWithTransfers.forget k).mapIso e.symm))

/-- The full inclusion in the bounded-above derived category. -/
abbrev effectiveMotivesMinusInclusion : EffectiveMotivesMinus k ⥤ DerivedCategory.Minus NST :=
  (effectiveCohomologyCondition k).ι

local notation "Ieff" => effectiveMotivesMinusInclusion k

/-- Nisnevich sheafification of the actual singular augmentation. -/
abbrev singularPresheafToEffectiveUnit :
    derivedNisnevichSheafification k ⟶ singularPresheafToEffective k ⋙ Ieff :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (η) (derivedNisnevichSheafification k)

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem bijective_comp_truncation (X : DerivedCategory.Minus PST)
    (Y : DerivedCategory PST) (b : ℤ) (hX : X.obj.IsLE b) :
    Function.Bijective (fun f : X ⟶ boundedTruncation k Y b =>
      f.hom ≫ (DerivedCategory.TStructure.t.truncLEι b).app Y) := by
  let t := DerivedCategory.TStructure.t (C := PST)
  let j : DerivedCategory.Minus PST ⥤ DerivedCategory PST := DerivedCategory.Minus.ι
  let : t.IsLE (j.obj X) b := hX
  let : t.IsLE X.obj b := hX
  constructor
  · intro f g h
    apply j.map_injective
    exact t.to_truncLE_obj_ext h
  · intro f
    exact ⟨ObjectProperty.homMk (t.liftTruncLE f b), t.liftTruncLE_ι f b⟩

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem exists_common_bound (X : DerivedCategory.Minus PST) :
    ∃ b : ℤ, X.obj.IsLE b ∧ ((Sing).obj X).obj.IsLE b := by
  obtain ⟨x, hx⟩ := X.property
  obtain ⟨y, hy⟩ := ((Sing).obj X).property
  let t := DerivedCategory.TStructure.t (C := PST)
  let : X.obj.IsLE x := hx
  let : ((Sing).obj X).obj.IsLE y := hy
  exact ⟨max x y, t.isLE_of_le X.obj x _ (le_max_left _ _),
    t.isLE_of_le ((Sing).obj X).obj y _ (le_max_right _ _)⟩

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

private theorem isA1Invariant_truncated_forget (K : EffectiveMotivesMinus k)
    (b i : ℤ) : ((DerivedCategory.homologyFunctor PST i).obj
      (boundedTruncation k ((U).obj K.obj.obj) b).obj).IsA1Invariant := by
  let R := (U).obj K.obj.obj
  let P := boundedTruncation k R b
  let H := DerivedCategory.homologyFunctor PST i
  by_cases hi : i ≤ b
  · obtain ⟨d, hd⟩ := K.obj.property
    let f := (DerivedCategory.TStructure.t.truncLEι b).app R
    let : IsIso (H.map f) := Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app b i hi R
    exact IsA1Invariant.of_iso
      (SheafWithTransfers.isA1Invariant_homology_forgetDerived k K.obj.obj d hd K.property i)
      (asIso (H.map f)).symm
  · exact isA1Invariant_of_isZero
      ((DerivedCategory.isLE_iff P.obj b).1 (inferInstanceAs (P.obj.IsLE b)) i (by omega))

private theorem bijective_precomp_singularUnit_derivedForget (P : DerivedCategory.Minus PST)
    (K : EffectiveMotivesMinus k) :
    Function.Bijective (fun f : ((Sing).obj P).obj ⟶ (U).obj K.obj.obj =>
      ((η).app P).hom ≫ f) := by
  obtain ⟨b, hP, hC⟩ := exists_common_bound k P
  let R := (U).obj K.obj.obj
  let Y := boundedTruncation k R b
  let j := (DerivedCategory.TStructure.t.truncLEι b).app R
  let x (f : P ⟶ Y) := f.hom ≫ j
  let y (f : (Sing).obj P ⟶ Y) := f.hom ≫ j
  let v (f : (Sing).obj P ⟶ Y) := (η).app P ≫ f
  let z (f : ((Sing).obj P).obj ⟶ R) := ((η).app P).hom ≫ f
  have hx : Function.Bijective x := bijective_comp_truncation k P R b hP
  have hy : Function.Bijective y := bijective_comp_truncation k ((Sing).obj P) R b hC
  have hv : Function.Bijective v := bijective_precomp_singularPresheafDerivedUnit k P Y
    (isA1Invariant_truncated_forget k K b)
  have h : z ∘ y = x ∘ v := funext fun f => (Category.assoc _ _ _).symm
  apply (Function.Bijective.of_comp_iff z hy).1
  rw [h]
  exact hx.comp hv

/-- Precomposition with the original Nisnevich singular augmentation is
bijective for every effective target. -/
theorem bijective_precomp_singularPresheafToEffectiveUnit (P : DerivedCategory.Minus PST)
    (K : EffectiveMotivesMinus k) :
    Function.Bijective (fun f : (singularPresheafToEffective k).obj P ⟶ K =>
      (singularPresheafToEffectiveUnit k).app P ≫ (Ieff).map f) := by
  let I := effectiveMotivesMinusToDerived k
  let adj := nisnevichDerivedAdjunction k
  let e₀ := (Functor.FullyFaithful.ofFullyFaithful I).homEquiv
    (X := (singularPresheafToEffective k).obj P) (Y := K)
  let e := e₀.trans (adj.homEquiv ((Sing).obj P).obj K.obj.obj)
  let J : DerivedCategory.Minus NST ⥤ DerivedCategory NST := DerivedCategory.Minus.ι
  let d := (Functor.FullyFaithful.ofFullyFaithful J).homEquiv
    (X := (derivedNisnevichSheafification k).obj P) (Y := K.obj)
  let e' := d.trans (adj.homEquiv P.obj K.obj.obj)
  let f (g : (singularPresheafToEffective k).obj P ⟶ K) :=
    (singularPresheafToEffectiveUnit k).app P ≫ (Ieff).map g
  let g (h : ((Sing).obj P).obj ⟶ (U).obj K.obj.obj) := ((η).app P).hom ≫ h
  have h : e' ∘ f = g ∘ e := by
    funext α
    change adj.homEquiv P.obj K.obj.obj (J.map (f α)) =
      g (adj.homEquiv ((Sing).obj P).obj K.obj.obj (I.map α))
    have hf : J.map (f α) = (a).mapDerivedCategory.map ((η).app P).hom ≫ I.map α := by
      dsimp only [f, singularPresheafToEffectiveUnit, NatTrans.comp_app,
        Functor.leftUnitor_inv_app, Functor.whiskerRight_app]
      rw [Category.id_comp]
      exact J.map_comp _ _
    rw [hf]
    exact adj.homEquiv_naturality_left ((η).app P).hom (I.map α)
  apply (Function.Bijective.of_comp_iff' e'.bijective f).1
  rw [h]
  exact (bijective_precomp_singularUnit_derivedForget k P K).comp e.bijective

private abbrev reflectionObject (K : DerivedCategory.Minus NST) : EffectiveMotivesMinus k :=
  (singularPresheafToEffective k).obj (presheafLift k K)

private def reflectionUnit (K : DerivedCategory.Minus NST) :
    K ⟶ (Ieff).obj (reflectionObject k K) :=
  (sheafificationPresheafLiftIso k K).inv ≫
    (singularPresheafToEffectiveUnit k).app (presheafLift k K)

private def reflectionHomEquiv (K : DerivedCategory.Minus NST) (E : EffectiveMotivesMinus k) :
    (reflectionObject k K ⟶ E) ≃ (K ⟶ (Ieff).obj E) :=
  Equiv.ofBijective (fun f => reflectionUnit k K ≫ (Ieff).map f) (by
    let e := sheafificationPresheafLiftIso k K
    have h := bijective_precomp_singularPresheafToEffectiveUnit k (presheafLift k K) E
    let f (g : reflectionObject k K ⟶ E) :=
      (singularPresheafToEffectiveUnit k).app (presheafLift k K) ≫ (Ieff).map g
    have hc : (fun g : reflectionObject k K ⟶ E => reflectionUnit k K ≫ (Ieff).map g) =
        e.homFromEquiv ∘ f := funext fun g => Category.assoc _ _ _
    exact hc.symm ▸ e.homFromEquiv.bijective.comp h)

private theorem reflectionHomEquiv_naturality (K : DerivedCategory.Minus NST)
    {E E' : EffectiveMotivesMinus k} (g : E ⟶ E') (f : reflectionObject k K ⟶ E) :
    reflectionHomEquiv k K E' (f ≫ g) =
      reflectionHomEquiv k K E f ≫ (Ieff).map g := by
  change reflectionUnit k K ≫ (Ieff).map (f ≫ g) =
    (reflectionUnit k K ≫ (Ieff).map f) ≫ (Ieff).map g
  rw [Functor.map_comp, Category.assoc]

/-- The bounded-above Nisnevich A¹-localization, computed by the original
singular total complex of a derived presheaf representative. -/
def effectiveReflection : DerivedCategory.Minus NST ⥤ EffectiveMotivesMinus k :=
  Adjunction.leftAdjointOfEquiv (reflectionHomEquiv k) (fun _ _ _ =>
    reflectionHomEquiv_naturality k _)

/-- Effective motives are reflective in the actual bounded-above derived category. -/
def effectiveReflectionAdjunction : effectiveReflection k ⊣ Ieff :=
  Adjunction.adjunctionOfEquivLeft (reflectionHomEquiv k) (fun _ _ _ =>
    reflectionHomEquiv_naturality k _)

/-- Reflection after exact sheafification is the original sheafified
singular construction. The component is the unique isomorphism under
the actual sheafified augmentations. -/
def sheafificationEffectiveReflectionIso :
    derivedNisnevichSheafification k ⋙ effectiveReflection k ≅
      singularPresheafToEffective k := by
  let M := effectiveReflection k
  let A := derivedNisnevichSheafification k
  let C' := singularPresheafToEffective k
  let u := singularPresheafToEffectiveUnit k
  let adj := effectiveReflectionAdjunction k
  let e (P : DerivedCategory.Minus PST) := adj.homEquiv (A.obj P) (C'.obj P)
  let f (P : DerivedCategory.Minus PST) := (e P).symm (u.app P)
  let g (P : DerivedCategory.Minus PST) :=
    (Equiv.ofBijective _ (bijective_precomp_singularPresheafToEffectiveUnit k P
      (M.obj (A.obj P)))).symm (adj.unit.app (A.obj P))
  have hf (P : DerivedCategory.Minus PST) :
      adj.unit.app (A.obj P) ≫ (Ieff).map (f P) = u.app P :=
    (e P).apply_symm_apply (u.app P)
  have hg (P : DerivedCategory.Minus PST) :
      u.app P ≫ (Ieff).map (g P) = adj.unit.app (A.obj P) :=
    (Equiv.ofBijective _ (bijective_precomp_singularPresheafToEffectiveUnit k P
      (M.obj (A.obj P)))).apply_symm_apply _
  let iso (P : DerivedCategory.Minus PST) : M.obj (A.obj P) ≅ C'.obj P :=
    { hom := f P
      inv := g P
      hom_inv_id := by
        apply (adj.homEquiv (A.obj P) (M.obj (A.obj P))).injective
        change adj.unit.app (A.obj P) ≫ (Ieff).map (f P ≫ g P) =
          adj.unit.app (A.obj P) ≫ (Ieff).map (𝟙 _)
        rw [Functor.map_comp, ← Category.assoc, hf, hg, (Ieff).map_id]
        exact (Category.comp_id (adj.unit.app (A.obj P))).symm
      inv_hom_id := by
        apply (bijective_precomp_singularPresheafToEffectiveUnit k P (C'.obj P)).1
        change u.app P ≫ (Ieff).map (g P ≫ f P) = u.app P ≫ (Ieff).map (𝟙 _)
        rw [Functor.map_comp, ← Category.assoc, hg, hf, (Ieff).map_id]
        exact (Category.comp_id (u.app P)).symm }
  refine NatIso.ofComponents iso ?_
  intro X Y m
  apply (adj.homEquiv (A.obj X) (C'.obj Y)).injective
  change adj.unit.app (A.obj X) ≫ (Ieff).map (M.map (A.map m) ≫ f Y) =
    adj.unit.app (A.obj X) ≫ (Ieff).map (f X ≫ C'.map m)
  calc
    _ = (A.map m ≫ adj.unit.app (A.obj Y)) ≫ (Ieff).map (f Y) := by
      have hm : A.map m ≫ adj.unit.app (A.obj Y) =
          adj.unit.app (A.obj X) ≫ (Ieff).map (M.map (A.map m)) :=
        adj.unit.naturality (A.map m)
      rw [Functor.map_comp, ← Category.assoc]
      exact congrArg (· ≫ (Ieff).map (f Y)) hm.symm
    _ = A.map m ≫ u.app Y := by rw [Category.assoc, hf]
    _ = u.app X ≫ (Ieff).map (C'.map m) := u.naturality m
    _ = _ := by rw [Functor.map_comp, ← Category.assoc, hf]

@[reassoc]
theorem sheafificationEffectiveReflectionIso_hom_unit (P : DerivedCategory.Minus PST) :
    (effectiveReflectionAdjunction k).unit.app ((derivedNisnevichSheafification k).obj P) ≫
      (Ieff).map ((sheafificationEffectiveReflectionIso k).hom.app P) =
    (singularPresheafToEffectiveUnit k).app P := by
  change (effectiveReflectionAdjunction k).homEquiv _ _ _ = _
  exact Equiv.apply_symm_apply _ _

/-- Effective reflection preserves each upper cohomological bound. -/
theorem effectiveReflection_isLE (K : DerivedCategory.Minus NST) (b : ℤ) (hb : K.obj.IsLE b) :
    ((effectiveMotivesMinusToDerived k).obj ((effectiveReflection k).obj K)).IsLE b := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_presheafLift_of_isLE k K b hb
  obtain ⟨L, hL, ⟨d⟩⟩ := exists_singularPresheafDerivedCochainObj_iso k P b hP
  let : L.IsStrictlyLE b := hL
  let N := ((singularTotalFunctor k).obj L)
  let : N.IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k L b
  let r := (singularPresheafDerivedCochainIso k L b).symm ≪≫ (Sing).mapIso d
  let j := DerivedCategory.Minus.ι (C := PST)
  let q := (singularPresheafDerivedCochainToQIso k N b).symm ≪≫ j.mapIso r
  let H := effectiveMotivesMinusToDerived k
  let t := DerivedCategory.TStructure.t (C := PST)
  let : (DerivedCategory.Q.obj N).IsLE b := inferInstance
  let : (((Sing).obj P).obj).IsLE b := t.isLE_of_iso q b
  have hC : (H.obj ((singularPresheafToEffective k).obj P)).IsLE b := by
    apply (DerivedCategory.isLE_iff _ b).2
    intro i hi
    let e := ((a).mapDerivedCategoryHomologyIso i).app ((Sing).obj P).obj
    exact ((a).map_isZero (DerivedCategory.isZero_of_isLE ((Sing).obj P).obj b i hi)).of_iso e
  let : (H.obj ((singularPresheafToEffective k).obj P)).IsLE b := hC
  let z := H.mapIso (((sheafificationEffectiveReflectionIso k).app P).symm ≪≫
    (effectiveReflection k).mapIso e)
  exact DerivedCategory.TStructure.t.isLE_of_iso z b

end AlgebraicGeometry.MotivicHomotopy
