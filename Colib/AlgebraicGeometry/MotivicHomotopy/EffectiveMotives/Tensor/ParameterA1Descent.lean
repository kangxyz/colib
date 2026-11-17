/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterNisnevichDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterInvariance
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.DerivedForgetInvariance
import Mathlib.CategoryTheory.Localization.Composition
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
import StacksFrontier.CategoryTheory.Triangulated.Localization.Pretriangulated

/-!
# Affine-line descent of the represented parameter tensor

Exact presheaf reindexing preserves invariant cohomology of derived
underlying coefficients. When testing the original singular augmentation
against a(k) bounded-above source, good upper truncation retains that
invariance. The actual sheafified tensor therefore preserves the
augmentation after effective reflection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "a(" K ")" => derivedNisnevichSheafification K
local notation "q(" K ")" => singularPresheafToEffective K
local notation "i(" K ")" => effectiveMotivesMinusInclusion K
local notation "j(" K ")" => effectiveMotivesMinusToDerived K
local notation "M(" K ")" => effectiveReflection K
local notation "U(" K ")" => forgetDerivedFunctor K
local notation "Sing(" K ")" => singularPresheafDerivedFunctor K
local notation "singη(" K ")" => singularPresheafDerivedUnit K
set_option quotPrecheck false in
local notation "t(" K ")" => (DerivedCategory.TStructure.t (C := PST(K)))
set_option quotPrecheck false in
local notation "d(" K ")" => DerivedCategory.Minus.ι (C := NST(K))

/-- The canonical abelian structure on the sheaf target. -/
local instance instAbelianParameterA1Descent : Abelian NST(k) := SheafWithTransfers.abelian k

variable {T : SmoothSite (Spec (.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

local notation "L(" F ")" => derivedParameterPushforward F
local notation "R(" comparison ")" => parameterSectionsDerived comparison
set_option quotPrecheck false in
local notation "B(" K "," F ")" => projectiveParameterNisnevichTensor (k := K) (F := F)
local notation "N(" comparison ")" => nisnevichParameterTensor comparison

omit [PerfectField k] in
/-- Parameter sections preserve derived underlying A¹-invariance when the
bounded-above input has strictly A¹-invariant homology sheaves. -/
theorem isA1Invariant_homology_parameterSectionsDerived_of_strict
    (K : DerivedCategory NST(k)) (b : ℤ) (hb : K.IsLE b)
    (hK : ∀ q, ((DerivedCategory.homologyFunctor NST(k) q).obj K).IsStrictA1Invariant)
    (i : ℤ) : ((DerivedCategory.homologyFunctor PST(k) i).obj
      ((U(k)).obj ((R(e)).obj K))).IsA1Invariant := by
  let V := additivePrecompose F
  let H := DerivedCategory.homologyFunctor PST(k) i
  let e₀ := (parameterSectionsDerivedForgetIso e).app K
  let e₁ := (V.mapDerivedCategoryHomologyIso i).app ((U(k)).obj K)
  have h := isA1Invariant_homology_forgetDerived_of_strict k K b hb hK i
  exact (additivePrecompose_isA1Invariant e _ h).of_iso ((H.mapIso e₀ ≪≫ e₁).symm)

private theorem isA1Invariant_homology_parameterSectionsDerived (K : EffectiveMotivesMinus k)
    (i : ℤ) : ((DerivedCategory.homologyFunctor PST(k) i).obj
      ((U(k)).obj ((R(e)).obj ((j(k)).obj K)))).IsA1Invariant := by
  obtain ⟨b, hb⟩ := K.obj.property
  exact isA1Invariant_homology_parameterSectionsDerived_of_strict e ((j(k)).obj K) b hb
    (fun q => isStrictA1Invariant_of_perfect _ (K.property q)) i

omit [PerfectField k] [HasDerivedCategory NST(k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem bijective_precomp_singularUnit_to_local
    (P : DerivedCategory.Minus PST(k)) (V : DerivedCategory PST(k))
    (hV : ∀ i : ℤ, ((DerivedCategory.homologyFunctor PST(k) i).obj V).IsA1Invariant) :
    Function.Bijective (fun f : ((Sing(k)).obj P).obj ⟶ V => ((singη(k)).app P).hom ≫ f) := by
  obtain ⟨n, hn⟩ := P.property
  obtain ⟨m, hm⟩ := ((Sing(k)).obj P).property
  let b := max n m
  let X := boundedTruncation k V b
  let j := ((t(k)).truncLEι b).app V
  let : P.obj.IsLE n := hn
  let : ((Sing(k)).obj P).obj.IsLE m := hm
  have hP : P.obj.IsLE b := (t(k)).isLE_of_le P.obj n b (le_max_left _ _)
  have hC : ((Sing(k)).obj P).obj.IsLE b := (t(k)).isLE_of_le _ m b (le_max_right _ _)
  have hX (i : ℤ) : ((DerivedCategory.homologyFunctor PST(k) i).obj X.obj).IsA1Invariant := by
    let H := DerivedCategory.homologyFunctor PST(k) i
    by_cases hi : i ≤ b
    · let : IsIso (H.map j) := Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app b i hi V
      exact (hV i).of_iso (asIso (H.map j)).symm
    · exact isA1Invariant_of_isZero (DerivedCategory.isZero_of_isLE X.obj b i (by omega))
  have hcomp (Y : DerivedCategory.Minus PST(k)) (hY : Y.obj.IsLE b) :
      Function.Bijective (fun f : Y ⟶ X => f.hom ≫ j) := by
    let I := DerivedCategory.Minus.ι (C := PST(k))
    let : (t(k)).IsLE (I.obj Y) b := hY
    constructor
    · intro f g hfg
      apply I.map_injective
      exact (t(k)).to_truncLE_obj_ext (n := b) (Y := I.obj Y) (X := V) hfg
    · intro f
      exact ⟨ObjectProperty.homMk ((t(k)).liftTruncLE f b), (t(k)).liftTruncLE_ι f b⟩
  let f (g : ((Sing(k)).obj P).obj ⟶ V) := ((singη(k)).app P).hom ≫ g
  let g (g : (Sing(k)).obj P ⟶ X) := g.hom ≫ j
  let h (g : P ⟶ X) := g.hom ≫ j
  let s (g : (Sing(k)).obj P ⟶ X) := (singη(k)).app P ≫ g
  have he : f ∘ g = h ∘ s := funext fun _ => (Category.assoc _ _ _).symm
  apply (Function.Bijective.of_comp_iff f (hcomp ((Sing(k)).obj P) hC)).1
  rw [he]
  exact (hcomp P hP).comp (bijective_precomp_singularPresheafDerivedUnit k P X hX)

private def effectiveParameterHomEquiv
    (P : DerivedCategory.Minus PST(k)) (K : EffectiveMotivesMinus k) :
    (((L(F) ⋙ q(k)).obj P) ⟶ K) ≃ (P.obj ⟶ (U(k)).obj ((R(e)).obj ((j(k)).obj K))) :=
  let s := (sheafificationEffectiveReflectionIso k).app ((L(F)).obj P)
  let a := (effectiveReflectionAdjunction k).homEquiv ((B(k,F)).obj P) K
  let d := (Functor.FullyFaithful.ofFullyFaithful (d(k))).homEquiv
    (X := (B(k,F)).obj P) (Y := (i(k)).obj K)
  (s.symm.homCongr (Iso.refl K)).trans
    (a.trans (d.trans (projectiveParameterNisnevichHomEquiv e P ((j(k)).obj K))))

private theorem effectiveParameterHomEquiv_precompose
    {P P' : DerivedCategory.Minus PST(k)} (f : P' ⟶ P) (K : EffectiveMotivesMinus k)
    (g : (L(F) ⋙ q(k)).obj P ⟶ K) :
    effectiveParameterHomEquiv e P' K ((L(F) ⋙ q(k)).map f ≫ g) =
      f.hom ≫ effectiveParameterHomEquiv e P K g := by
  let r := sheafificationEffectiveReflectionIso k
  let A := effectiveReflectionAdjunction k
  let v := r.hom.app ((L(F)).obj P) ≫ g
  have hv : r.hom.app ((L(F)).obj P') ≫ (L(F) ⋙ q(k)).map f ≫ g =
      (M(k)).map ((B(k,F)).map f) ≫ v := by
    exact (r.hom.naturality_assoc ((L(F)).map f) g).symm
  let U := L(F) ⋙ q(k)
  let V := L(F) ⋙ a(k) ⋙ M(k)
  let b (Y : DerivedCategory.Minus PST(k)) :=
    projectiveParameterNisnevichHomEquiv e Y ((j(k)).obj K)
  let T := projectiveParameterNisnevichTensor (k := k) (F := F)
  let J := d(k)
  let c (Y : DerivedCategory.Minus PST(k)) := A.homEquiv (T.obj Y) K
  let ρ (Y : DerivedCategory.Minus PST(k)) (f : U.obj Y ⟶ K) : V.obj Y ⟶ K :=
    (r.symm.app ((L(F)).obj Y)).homCongr (Iso.refl K) f
  have hρ (Y : DerivedCategory.Minus PST(k)) (f : U.obj Y ⟶ K) :
      ρ Y f = r.hom.app ((L(F)).obj Y) ≫ f := by
    dsimp [ρ, Iso.homCongr]
    exact congrArg (r.hom.app ((L(F)).obj Y) ≫ ·) (Category.comp_id f)
  change b P' (J.map (c P' (ρ P' (U.map f ≫ g)))) =
    f.hom ≫ b P (J.map (c P (ρ P g)))
  rw [hρ, hρ, hv]
  change b P' (J.map (A.homEquiv _ _ ((M(k)).map (T.map f) ≫ v))) =
    f.hom ≫ b P (J.map (A.homEquiv _ _ v))
  rw [A.homEquiv_naturality_left, J.map_comp]
  exact projectiveParameterNisnevichHomEquiv_precompose e ((j(k)).obj K) f
    (J.map (A.homEquiv _ _ v))

set_option maxHeartbeats 1500000 in
-- The adjunction compares bounded presheaf, sheaf, and effective hom sets.
/-- Tensoring the original singular augmentation with this represented
parameter gives an isomorphism after effective localization. -/
theorem isIso_singularPresheafToEffective_map_parameter_singularUnit
    (comparison : Cor.graphFunctor k ⋙ F ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (P : DerivedCategory.Minus PST(k)) :
    IsIso ((L(F) ⋙ q(k)).map ((singη(k)).app P)) := by
  apply isIso_of_coyoneda_map_bijective
  intro K
  let V := (U(k)).obj ((R(comparison)).obj ((j(k)).obj K))
  let b := effectiveParameterHomEquiv comparison P K
  let b' := effectiveParameterHomEquiv comparison ((Sing(k)).obj P) K
  let f (g : (L(F) ⋙ q(k)).obj ((Sing(k)).obj P) ⟶ K) :=
    (L(F) ⋙ q(k)).map ((singη(k)).app P) ≫ g
  let g (g : ((Sing(k)).obj P).obj ⟶ V) := ((singη(k)).app P).hom ≫ g
  have h : b ∘ f = g ∘ b' :=
    funext (effectiveParameterHomEquiv_precompose comparison ((singη(k)).app P) K)
  apply (Function.Bijective.of_comp_iff' b.bijective f).1
  rw [h]
  exact (bijective_precomp_singularUnit_to_local P V
    (isA1Invariant_homology_parameterSectionsDerived comparison K)).comp b'.bijective

private theorem isIso_effectiveReflection_map_nisnevichParameter_unit
    (K : DerivedCategory.Minus NST(k)) :
    IsIso ((N(e) ⋙ M(k)).map ((effectiveReflectionAdjunction k).unit.app K)) := by
  let P := presheafLift k K
  let d := sheafificationPresheafLiftIso k K
  let E := effectiveReflectionAdjunction k
  let r := sheafificationEffectiveReflectionIso k
  let j := (i(k)).map (r.hom.app P)
  let z := (singularPresheafToEffectiveUnit k).app P
  let z₀ := (a(k)).map ((singη(k)).app P)
  have h : E.unit.app K ≫ (i(k)).map ((M(k)).map d.inv) ≫ j = d.inv ≫ z := by
    have hn := E.unit.naturality_assoc d.inv j
    change d.inv ≫ E.unit.app ((a(k)).obj P) ≫ j =
      E.unit.app K ≫ (i(k)).map ((M(k)).map d.inv) ≫ j at hn
    exact hn.symm.trans (congrArg (d.inv ≫ ·) (sheafificationEffectiveReflectionIso_hom_unit k P))
  have hz : z = z₀ := by
    change 𝟙 _ ≫ z₀ = z₀
    exact Category.id_comp _
  have he : a(k) ⋙ N(e) ⋙ M(k) ≅ L(F) ⋙ q(k) :=
    (Functor.associator a(k) N(e) M(k)).symm ≪≫
      Functor.isoWhiskerRight (nisnevichParameterTensorCompIso e) M(k) ≪≫
      Functor.associator L(F) a(k) M(k) ≪≫ Functor.isoWhiskerLeft L(F) r
  have h₀ : IsIso ((N(e) ⋙ M(k)).map z₀) :=
    (NatIso.isIso_map_iff he ((singη(k)).app P)).2
      (isIso_singularPresheafToEffective_map_parameter_singularUnit e P)
  let : IsIso ((N(e) ⋙ M(k)).map z) := hz.symm ▸ h₀
  let y := (i(k)).map ((M(k)).map d.inv) ≫ j
  have hy : IsIso ((N(e) ⋙ M(k)).map (E.unit.app K) ≫ (N(e) ⋙ M(k)).map y) := by
    rw [← Functor.map_comp, show E.unit.app K ≫ y = d.inv ≫ z from h, Functor.map_comp]
    infer_instance
  let : IsIso ((N(e) ⋙ M(k)).map y) := inferInstance
  exact (isIso_comp_right_iff _ _).1 hy

/-- The actual reflected tensor on bounded-above effective motives, with
the given represented parameter. -/
def effectiveParameterTensor : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k :=
  i(k) ⋙ N(e) ⋙ M(k)

/-- The tensor on effective motives factors the actual projective tensor
through the original Nisnevich and affine-line reflections. -/
@[no_expose]
def effectiveParameterTensorCompIso : q(k) ⋙ effectiveParameterTensor e ≅ L(F) ⋙ q(k) := by
  let u := Functor.whiskerRight (effectiveReflectionAdjunction k).unit (N(e) ⋙ M(k))
  let : ∀ K, IsIso (u.app K) := isIso_effectiveReflection_map_nisnevichParameter_unit e
  let : IsIso u := NatIso.isIso_of_isIso_app _
  let r := sheafificationEffectiveReflectionIso k
  exact Functor.isoWhiskerRight r.symm (i(k) ⋙ N(e) ⋙ M(k)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft a(k)
      ((Functor.associator M(k) i(k) (N(e) ⋙ M(k))).symm ≪≫
        (asIso u).symm ≪≫ Functor.leftUnitor _) ≪≫
    (Functor.associator a(k) N(e) M(k)).symm ≪≫
    Functor.isoWhiskerRight (nisnevichParameterTensorCompIso e) M(k) ≪≫
    Functor.associator L(F) a(k) M(k) ≪≫
    Functor.isoWhiskerLeft L(F) r

instance : (effectiveParameterTensor e).CommShift ℤ := by
  unfold effectiveParameterTensor
  infer_instance

instance : (effectiveParameterTensor e).IsTriangulated := by
  unfold effectiveParameterTensor
  infer_instance

end AlgebraicGeometry.MotivicHomotopy
