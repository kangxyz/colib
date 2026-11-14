/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ProjectiveRepresentatives

/-! # The original shifted single-source representative and its cancellation -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
universe w v u
namespace Stacks.Cohomology.Corepresented
variable {A : Type u} [Category.{v} A] [Abelian A] (Z G : A)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Cancelling the actual minus-one shift of the original representative gives its single map. -/
lemma equivHomShift_single_cancel
    (z : Cocycle ((CochainComplex.singleFunctor A 0).obj Z)
      (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) 1) :
    Cocycle.equivHomShift.symm z ≫
      (shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by decide)).hom.app
        ((CochainComplex.singleFunctor A 0).obj G) =
      (CochainComplex.singleFunctor A 0).map
        (Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom) := by
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective z 1 (zero_add 1) 2 rfl
  erw [Cochain.fromSingleEquiv_fromSingleMk f (zero_add 1)]
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f]
  erw [equivHomShift_fromSingleMk_f_zero Z _ 1 f hf]
  simp [shiftFunctorCompIsoId,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.singleFunctor, HomologicalComplex.single_map_f_self]

variable [HasDerivedCategory.{w} A]

/-- Native derived cancellation of the original single complex shifted by minus one. -/
def derivedSingleNegOneCancelIso :
    (DerivedCategory.Q.obj (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor A 0).obj G :=
  (shiftFunctor _ (1 : ℤ)).mapIso
      ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app ((CochainComplex.singleFunctor A 0).obj G)) ≪≫
    (shiftFunctorCompIsoId (DerivedCategory A) (-1 : ℤ) 1 (by decide)).app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj G)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app G).symm

/-- The actual localized representative cancels to the derived single map of its unit coordinate. -/
lemma localized_single_cocycle_cancel
    (z : Cocycle ((CochainComplex.singleFunctor A 0).obj Z)
      (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) 1) :
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app Z).hom ≫
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) ≫
      (derivedSingleNegOneCancelIso G).hom =
      (DerivedCategory.singleFunctor A 0).map
        (Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom) := by
  dsimp only [derivedSingleNegOneCancelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom]
  rw [← Functor.map_shiftFunctorCompIsoId_hom_app_assoc,
    ← DerivedCategory.Q.map_comp_assoc, equivHomShift_single_cancel]
  erw [← (DerivedCategory.singleFunctorIsoCompQ A 0).hom.naturality_assoc]
  simp

end Stacks.Cohomology.Corepresented
