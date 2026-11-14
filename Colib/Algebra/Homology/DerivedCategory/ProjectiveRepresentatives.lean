/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ProjectiveCorepresented

/-! # Actual cocycle representatives for projectively corepresented cohomology -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
universe w v u
namespace Stacks.Cohomology.Corepresented
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] (Z : A) [Projective Z]
  (e : preadditiveCoyoneda.obj (op Z) ≅ T)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original projective comparison localizes the actual Hom-complex cocycle representative. -/
lemma projectiveHomologyDerivedAddEquiv_cocycle (L : CochainComplex A ℤ) (n : ℤ)
    (z : Cocycle ((CochainComplex.singleFunctor A 0).obj Z) L n) :
    projectiveHomologyDerivedAddEquiv T Z e L n
      (HomologicalComplex.homologyMap (corepresentedHomComplexIso T Z e L).hom n
        ((homologyAddEquiv _ L n).symm (CohomologyClass.mk z))) =
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app Z).hom ≫
        DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := by
  rw [projectiveHomologyDerivedAddEquiv_apply]
  have h : corepresentedHomologyHomotopyAddEquiv T Z e L n
      (HomologicalComplex.homologyMap (corepresentedHomComplexIso T Z e L).hom n
        ((homologyAddEquiv _ L n).symm (CohomologyClass.mk z))) =
      (HomotopyCategory.quotient A (.up ℤ)).map (Cocycle.equivHomShift.symm z) := by
    change homComplexHomologyAddEquiv _ L n
      (HomologicalComplex.homologyMap (corepresentedHomComplexIso T Z e L).inv n
        (HomologicalComplex.homologyMap (corepresentedHomComplexIso T Z e L).hom n
          ((homologyAddEquiv _ L n).symm (CohomologyClass.mk z)))) = _
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp]
    simp only [Iso.hom_inv_id, HomologicalComplex.homologyMap_id, ConcreteCategory.id_apply]
    simp only [homComplexHomologyAddEquiv, AddEquiv.trans_apply,
      AddEquiv.apply_symm_apply, CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk]
  rw [h]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc, Iso.inv_hom_id_app_assoc]

omit [HasDerivedCategory.{w} A] [Projective Z] in
/-- The actual corepresentation reads the unique nonzero source coordinate. -/
lemma corepresentedHomComplexIso_hom_fromSingleMk (L : CochainComplex A ℤ) (n : ℤ)
    (f : Z ⟶ L.X n) :
    (corepresentedHomComplexIso T Z e L).hom.f n (Cochain.fromSingleMk f (zero_add n)) =
      e.hom.app (L.X n) f := by
  change e.hom.app (L.X n)
    (Cochain.fromSingleEquiv (zero_add n) (Cochain.fromSingleMk f (zero_add n))) = _
  rw [Cochain.fromSingleEquiv_fromSingleMk]

omit [HasDerivedCategory.{w} A] [Projective Z] in
/-- The original shifted morphism reads the actual single-source coordinate without a sign. -/
lemma equivHomShift_fromSingleMk_f_zero (L : CochainComplex A ℤ) (n : ℤ)
    (f : Z ⟶ L.X n) (hf : f ≫ L.d n (n + 1) = 0) :
    (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).hom ≫ f ≫
        (L.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv := by
  change ((Cochain.fromSingleMk f (zero_add n)).rightShift n 0 (zero_add n)).v
    0 0 (add_zero 0) = _
  rw [Cochain.rightShift_v (Cochain.fromSingleMk f (zero_add n))
    n 0 (zero_add n) 0 0 (add_zero 0) n (zero_add n), Cochain.fromSingleMk_v]
  simp only [Category.assoc]

omit [HasDerivedCategory.{w} A] in
/-- The native Hom-complex class is represented by its canonical cycle lift. -/
lemma homologyAddEquiv_symm_mk (K L : CochainComplex A ℤ) (n : ℤ)
    (z : Cocycle K L n) :
    (homologyAddEquiv K L n).symm (CohomologyClass.mk z) =
      (K.HomComplex L).homologyπ n ((leftHomologyData K L n).cyclesIso.inv z) := by
  exact ConcreteCategory.congr_hom (leftHomologyData K L n).π_comp_homologyIso_inv z

include T e in
/-- Every derived map from the original projective single source
has an actual cocycle representative. -/
lemma projectiveDerived_cocycle_surjective (L : CochainComplex A ℤ) (n : ℤ)
    (x : (DerivedCategory.singleFunctor A 0).obj Z ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    ∃ z : Cocycle ((CochainComplex.singleFunctor A 0).obj Z) L n,
      x = ((DerivedCategory.singleFunctorIsoCompQ A 0).app Z).hom ≫
        DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := by
  obtain ⟨a, rfl⟩ := (projectiveHomologyDerivedAddEquiv T Z e L n).surjective x
  obtain ⟨b, rfl⟩ := (HomologicalComplex.homologyMapIso
    (corepresentedHomComplexIso T Z e L) n).addCommGroupIsoToAddEquiv.surjective a
  obtain ⟨c, rfl⟩ :=
    (homologyAddEquiv ((CochainComplex.singleFunctor A 0).obj Z) L n).symm.surjective b
  obtain ⟨z, rfl⟩ := c.mk_surjective
  exact ⟨z, projectiveHomologyDerivedAddEquiv_cocycle T Z e L n z⟩

end Stacks.Cohomology.Corepresented
