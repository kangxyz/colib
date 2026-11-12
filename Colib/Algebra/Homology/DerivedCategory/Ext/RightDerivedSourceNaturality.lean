/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived
public import Colib.CategoryTheory.Abelian.RightDerived.CochainNaturality

/-!
# Source naturality of the native Ext and right-derived comparison

Precomposition by the actual source morphism agrees with the actual derived
natural transformation of additive Hom. The proof uses native `extMk`
representatives and their literal cycle projections. It does not replace Ext,
the injective resolution, or the existing comparison.

The source-natural statement is adapted from
`Motivic/Aglib/Algebra/Homology/DerivedCategory/ExtRightDerivedFunctoriality.lean`
at `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`14967eefc2b712dbbf48c20db5e1134d186523d8`. The proof follows the already native
coefficient-natural proof
in `Colib/Algebra/Homology/DerivedCategory/Ext/RightDerivedNaturality.lean` at
`db74eb2403109105cc51ceba1a4e8a8391a4543c`, using the source map in place of a
resolution lift.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex

universe u v w

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

private theorem sourceExtMk_cochain_closed (a : X ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫
      I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
  rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, zero_comp] using
    congrArg (fun k => k ≫
      (I.cochainComplexXIso ((n : ℤ) + 1) (n + 1) (by omega)).inv) ha

variable [EnoughInjectives C] [HasExt.{w} C]

private theorem sourceExtRightDerivedAddEquiv_extMk_homology
    (a : X ⟶ I.cocomplex.X n) (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    I.extRightDerivedAddEquiv X n (I.extMk a (n + 1) rfl ha) =
      let H := coyonedaComplex X I.cochainComplex
      (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
        (H.homologyπ (n : ℤ) ((H.sc (n : ℤ)).abCyclesIso.inv
          ⟨a ≫ (I.cochainComplexXIso n n rfl).inv, by
            change (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫
              I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
            rw [CochainComplex.next ℤ (n : ℤ)]
            exact I.sourceExtMk_cochain_closed X n a ha⟩)) := by
  simpa only [extMk, Nat.cast_add, Nat.cast_one] using I.extRightDerivedAddEquiv_cocycle X n
    (a ≫ (I.cochainComplexXIso n n rfl).inv) (I.sourceExtMk_cochain_closed X n a ha)

/-- The existing comparison intertwines original Yoneda precomposition and the
actual right-derived natural transformation, with independent Ext universe. -/
theorem extRightDerivedAddEquiv_naturality_left
    {X' : C} (f : X' ⟶ X) (x : Abelian.Ext.{w} X Y n) :
    I.extRightDerivedAddEquiv X' n ((Abelian.Ext.mk₀ f).comp x (zero_add n)) =
      (NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y
        (I.extRightDerivedAddEquiv X n x) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let G := preadditiveCoyoneda.obj (Opposite.op X')
  let H₀ := coyonedaComplex X I.cochainComplex
  let H₁ := coyonedaComplex X' I.cochainComplex
  let ψ := (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map f.op)
    (.up ℤ)).app I.cochainComplex
  have ha' : (f ≫ a) ≫ I.cocomplex.d n (n + 1) = 0 := by
    rw [Category.assoc, ha, comp_zero]
  let z₀ : H₀.cycles (n : ℤ) := (H₀.sc (n : ℤ)).abCyclesIso.inv
    ⟨a ≫ (I.cochainComplexXIso n n rfl).inv, by
      change (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫
        I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
      rw [CochainComplex.next ℤ (n : ℤ)]
      exact I.sourceExtMk_cochain_closed X n a ha⟩
  let z₁ : H₁.cycles (n : ℤ) := (H₁.sc (n : ℤ)).abCyclesIso.inv
    ⟨(f ≫ a) ≫ (I.cochainComplexXIso n n rfl).inv, by
      change ((f ≫ a) ≫ (I.cochainComplexXIso n n rfl).inv) ≫
        I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
      rw [CochainComplex.next ℤ (n : ℤ)]
      exact I.sourceExtMk_cochain_closed X' n (f ≫ a) ha'⟩
  have hi₀ : H₀.iCycles (n : ℤ) z₀ = a ≫ (I.cochainComplexXIso n n rfl).inv := by
    dsimp only [z₀]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  have hi₁ : H₁.iCycles (n : ℤ) z₁ =
      (f ≫ a) ≫ (I.cochainComplexXIso n n rfl).inv := by
    dsimp only [z₁]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  have hc : cyclesMap ψ (n : ℤ) z₀ = z₁ := by
    apply (AddCommGrpCat.mono_iff_injective (H₁.iCycles (n : ℤ))).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hi₀, hi₁]
    change f ≫ (a ≫ (I.cochainComplexXIso n n rfl).inv) =
      (f ≫ a) ≫ (I.cochainComplexXIso n n rfl).inv
    exact (Category.assoc _ _ _).symm
  have hH : homologyMap ψ (n : ℤ) (H₀.homologyπ (n : ℤ) z₀) =
      H₁.homologyπ (n : ℤ) z₁ := by
    rw [← ConcreteCategory.comp_apply, homologyπ_naturality,
      ConcreteCategory.comp_apply, hc]
  rw [mk₀_comp_extMk, sourceExtRightDerivedAddEquiv_extMk_homology,
    sourceExtRightDerivedAddEquiv_extMk_homology]
  change (I.isoRightDerivedObjCochain G n).inv (H₁.homologyπ (n : ℤ) z₁) =
    (NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y
      ((I.isoRightDerivedObjCochain F n).inv (H₀.homologyπ (n : ℤ) z₀))
  rw [rightDerived_app_eq_cochain (preadditiveCoyoneda.map f.op) I n]
  simp only [ConcreteCategory.comp_apply]
  have hcancel : (I.isoRightDerivedObjCochain F n).hom
      ((I.isoRightDerivedObjCochain F n).inv (H₀.homologyπ (n : ℤ) z₀)) =
      H₀.homologyπ (n : ℤ) z₀ :=
    ConcreteCategory.congr_hom (I.isoRightDerivedObjCochain F n).inv_hom_id _
  rw [hcancel]
  exact congrArg (fun y => (I.isoRightDerivedObjCochain G n).inv y) hH.symm

end CategoryTheory.InjectiveResolution
