/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingularTotal
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
import StacksFrontier.Algebra.Homology.DerivedCategory.Basic

/-!
# Singularization on bounded-above derived transfer presheaves

The original singular totalization factors through the bounded-above
derived category. Its value has the effective cohomology condition.
-/

public noncomputable section

open CategoryTheory

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "c" => ComplexShape.up ℤ

private def singularSheafTotalHomotopyToDerived
    [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)] :
    HomotopyCategory (PresheafWithTransfers.{u + 1} k) c ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) :=
  CategoryTheory.Quotient.lift (homotopic _ c) (singularSheafTotalFunctor k ⋙ DerivedCategory.Q)
    (fun _ _ _ _ ⟨h⟩ => DerivedCategory.Q_map_eq_of_homotopy (SheafWithTransfers.{u + 1} k)
      (singularSheafTotalHomotopy k h))

/-- Quasi-isomorphisms of the actual bounded-above homotopy category. -/
abbrev transferHomotopyMinusQuasiIso :
    MorphismProperty (HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k)) :=
  (HomotopyCategory.quasiIso (PresheafWithTransfers.{u + 1} k) c).inverseImage
    (HomotopyCategory.Minus.ι _)

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

private theorem exists_transferHomotopyMinusLocalization :
    ∃ Q : HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k),
      Nonempty (Q ⋙ DerivedCategory.Minus.ι ≅
        HomotopyCategory.Minus.ι _ ⋙ DerivedCategory.Qh) ∧
      Q.IsLocalization (transferHomotopyMinusQuasiIso k) :=
  (HomotopyCategory.isSaturated_subcategoryAcyclic_inverseImage_and_quasiIso_and_isLocalization
    (A := PresheafWithTransfers.{u + 1} k)
    (D := DerivedCategory (PresheafWithTransfers.{u + 1} k))).2.2.1

/-- The bounded-above localization of the actual homotopy category. -/
def transferHomotopyMinusLocalization :
    HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (exists_transferHomotopyMinusLocalization k).choose

instance : (transferHomotopyMinusLocalization k).IsLocalization
    (transferHomotopyMinusQuasiIso k) :=
  (exists_transferHomotopyMinusLocalization k).choose_spec.2

/-- The bounded-above localization is induced by the original quotient. -/
def transferHomotopyMinusLocalizationIso :
    transferHomotopyMinusLocalization k ⋙ DerivedCategory.Minus.ι ≅
      HomotopyCategory.Minus.ι _ ⋙ DerivedCategory.Qh :=
  (exists_transferHomotopyMinusLocalization k).choose_spec.1.some

omit [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)] in
private theorem exists_cochain_of_homotopyMinus
    (K : HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    ∃ (L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ), L.IsStrictlyLE b ∧
      (HomotopyCategory.quotient _ c).obj L = K.obj := by
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
  have h := K.property
  rw [← hL, HomotopyCategory.minus_quotient_obj_iff, CochainComplex.minus_iff] at h
  obtain ⟨b, h⟩ := h
  exact ⟨L, b, h, hL⟩

variable [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- The singular total functor before localization at quasi-isomorphisms. -/
def singularSheafTotalHomotopyMinus :
    HomotopyCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤ EffectiveMotivesMinus k := by
  let F := HomotopyCategory.Minus.ι (PresheafWithTransfers.{u + 1} k) ⋙
    singularSheafTotalHomotopyToDerived k
  let D := DerivedCategory.TStructure.t (C := SheafWithTransfers.{u + 1} k)
  let G := D.minus.lift F fun K => by
    obtain ⟨L, b, hb, e⟩ := exists_cochain_of_homotopyMinus k K
    let : L.IsStrictlyLE b := hb
    let N := (singularSheafTotalFunctor k).obj L
    let : N.IsStrictlyLE b := singularSheafTotalFunctor_obj_isStrictlyLE k L b
    have h : (DerivedCategory.Q.obj N).IsLE b := inferInstance
    change ∃ n, ((singularSheafTotalHomotopyToDerived k).obj K.obj).IsLE n
    exact ⟨b, e ▸ h⟩
  exact (effectiveCohomologyCondition k).lift G fun K i => by
    obtain ⟨L, b, hb, e⟩ := exists_cochain_of_homotopyMinus k K
    let : L.IsStrictlyLE b := hb
    change ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i).obj
      ((singularSheafTotalHomotopyToDerived k).obj K.obj)).obj.IsA1Invariant
    exact e ▸ singularSheafTotalDerivedCohomology_isA1Invariant k L b i

omit [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)] in
private theorem singularSheafTotalHomotopyMinus_inverts :
    (transferHomotopyMinusQuasiIso k).IsInvertedBy (singularSheafTotalHomotopyMinus k) := by
  intro K L f hf
  obtain ⟨K₀, a, ha, e⟩ := exists_cochain_of_homotopyMinus k K
  obtain ⟨L₀, b, hb, d⟩ := exists_cochain_of_homotopyMinus k L
  let q := HomotopyCategory.quotient (PresheafWithTransfers.{u + 1} k) c
  let g : q.obj K₀ ⟶ q.obj L₀ := eqToHom e ≫ f.hom ≫ eqToHom d.symm
  obtain ⟨f₀, h₀⟩ := q.map_surjective g
  have hg : HomotopyCategory.quasiIso (PresheafWithTransfers.{u + 1} k) c g := by
    exact MorphismProperty.comp_mem _ _ _
      ((HomotopyCategory.quasiIso _ _).of_isIso _)
      (MorphismProperty.comp_mem _ _ _ hf ((HomotopyCategory.quasiIso _ _).of_isIso _))
  have hq : QuasiIso f₀ := by
    rw [← h₀, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] at hg
    exact hg
  let : K₀.IsStrictlyLE a := ha
  let : L₀.IsStrictlyLE b := hb
  let : K₀.IsStrictlyLE (max a b) := K₀.isStrictlyLE_of_le a _ (le_max_left _ _)
  let : L₀.IsStrictlyLE (max a b) := L₀.isStrictlyLE_of_le b _ (le_max_right _ _)
  let : QuasiIso f₀ := hq
  let : QuasiIso ((singularSheafTotalFunctor k).map f₀) :=
    singularSheafTotalFunctor_quasiIso k f₀ (max a b)
  let S := singularSheafTotalHomotopyToDerived k
  have hs : IsIso (S.map g) := by
    rw [← h₀]
    change IsIso (DerivedCategory.Q.map ((singularSheafTotalFunctor k).map f₀))
    infer_instance
  have hmap : IsIso (S.map f.hom) := by
    change IsIso (S.map (eqToHom e ≫ f.hom ≫ eqToHom d.symm)) at hs
    rw [Functor.map_comp, Functor.map_comp] at hs
    let : IsIso (S.map f.hom ≫ S.map (eqToHom d.symm)) :=
      IsIso.of_isIso_comp_left (S.map (eqToHom e)) _
    exact IsIso.of_isIso_comp_right _ (S.map (eqToHom d.symm))
  let I := effectiveMotivesMinusToDerived k
  have : IsIso (I.map ((singularSheafTotalHomotopyMinus k).map f)) := hmap
  exact isIso_of_reflects_iso _ I

/-- The original singular total construction on bounded-above derived
transfer presheaves, with values in the native effective motives. -/
def singularDerivedEffectiveFunctor :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤ EffectiveMotivesMinus k :=
  Localization.lift (singularSheafTotalHomotopyMinus k)
    (singularSheafTotalHomotopyMinus_inverts k) (transferHomotopyMinusLocalization k)

/-- The defining comparison on the original bounded-above complexes. -/
def singularDerivedEffectiveFunctorFactors :
    transferHomotopyMinusLocalization k ⋙ singularDerivedEffectiveFunctor k ≅
      singularSheafTotalHomotopyMinus k :=
  Localization.fac (singularSheafTotalHomotopyMinus k)
    (singularSheafTotalHomotopyMinus_inverts k) (transferHomotopyMinusLocalization k)

end AlgebraicGeometry.MotivicHomotopy
