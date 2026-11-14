/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ProjectiveSingleCoordinate
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.KernelFunctor

/-! # Native exact-functor transport of shifted single sources -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex.finiteCoefficients
universe w w' v u v' u'
namespace Stacks.Cohomology.Corepresented
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
variable [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

omit [PreservesFiniteLimits F] in
/-- The original shifted-single functor iso preserves the native minus-one/one cancellation. -/
lemma shiftedSingleFunctorIso_cancel (G : A) (H : B) (e : F.obj G ≅ H) :
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app
        (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) ≫
      ((shiftedSingleFunctorIso F G H e).hom)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by decide)).hom.app
        ((CochainComplex.singleFunctor B 0).obj H) =
    (F.mapHomologicalComplex (.up ℤ)).map
      ((shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by decide)).hom.app
        ((CochainComplex.singleFunctor A 0).obj G)) ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app G ≫
      (CochainComplex.singleFunctor B 0).map e.hom := by
  let R := F.mapHomologicalComplex (.up ℤ)
  let K := (CochainComplex.singleFunctor A 0).obj G
  let L := (CochainComplex.singleFunctor B 0).obj H
  let f := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app G ≫
    (CochainComplex.singleFunctor B 0).map e.hom
  have h := (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1
    (by decide)).hom.naturality f
  change (f⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by decide)).hom.app L =
    (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by decide)).hom.app (R.obj K) ≫ f at h
  change (R.commShiftIso (1 : ℤ)).hom.app (K⟦(-1 : ℤ)⟧) ≫
    ((R.commShiftIso (-1 : ℤ)).hom.app K ≫ f⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by decide)).hom.app L =
    R.map ((shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1
      (by decide)).hom.app K) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  rw [h, ← Functor.map_shiftFunctorCompIsoId_hom_app_assoc]

variable [PreservesFiniteColimits F] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- The original exact derived/source transport localizes the original transported cochain map. -/
@[reassoc]
lemma derivedSourceTransport_localized (Z : A) (Z' : B) (α : Z' ⟶ F.obj Z)
    (K : CochainComplex A ℤ) (n : ℤ)
    (f : (CochainComplex.singleFunctor A 0).obj Z ⟶ K⟦n⟧) :
    (DerivedCategory.singleFunctor B 0).map α ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app Z ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map f ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K) ≫
      (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj K) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧' =
    DerivedCategory.Q.map
      ((CochainComplex.singleFunctor B 0).map α ≫
        (F.mapCochainComplexSingleFunctor 0).inv.app Z ≫
        (F.mapHomologicalComplex (.up ℤ)).map f ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  have h := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom n K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
  change F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app K) ≫
    (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj K) ≫
    (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧' =
    F.mapDerivedCategoryFactors.hom.app (K⟦n⟧) ≫
    DerivedCategory.Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) at h
  simp only [Functor.map_comp, Category.assoc]
  rw [h, F.mapDerivedCategoryFactors_hom_naturality_assoc,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  rfl

/-- Exact transport of the original weight-one representative cancels to its actual section map. -/
lemma derivedSourceTransport_single_cancel (Z G : A) (Z' H : B)
    (α : Z' ⟶ F.obj Z) (e : F.obj G ≅ H)
    (z : CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor A 0).obj Z)
      (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) 1) :
    let K := ((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧
    (DerivedCategory.singleFunctor B 0).map α ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app Z ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj K) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.map (shiftedSingleFunctorIso F G H e).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso H).hom =
    (DerivedCategory.singleFunctor B 0).map
      (α ≫ F.map (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom) ≫ e.hom) := by
  dsimp only
  let R := F.mapHomologicalComplex (.up ℤ)
  let f := CochainComplex.HomComplex.Cocycle.equivHomShift.symm z
  let g := CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom
  have hc :
      (CochainComplex.singleFunctor B 0).map α ≫
        (F.mapCochainComplexSingleFunctor 0).inv.app Z ≫ R.map f ≫
        (R.commShiftIso (1 : ℤ)).hom.app
          (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) ≫
        ((shiftedSingleFunctorIso F G H e).hom)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by decide)).hom.app
          ((CochainComplex.singleFunctor B 0).obj H) =
      (CochainComplex.singleFunctor B 0).map (α ≫ F.map g ≫ e.hom) := by
    rw [shiftedSingleFunctorIso_cancel]
    rw [← R.map_comp_assoc, equivHomShift_single_cancel]
    erw [(HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.naturality_assoc]
    simp [Functor.mapCochainComplexSingleFunctor, Functor.map_comp, Category.assoc, g]
  rw [derivedSourceTransport_localized_assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  dsimp only [derivedSingleNegOneCancelIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom]
  rw [← Functor.map_shiftFunctorCompIsoId_hom_app_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc]
  simp only [Category.assoc]
  erw [hc]
  change (DerivedCategory.singleFunctor B 0).map (α ≫ F.map g ≫ e.hom) ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- Exact source transport on the actual canonical single representative preserves its section. -/
lemma derivedSourceTransport_singleMap_cancel (Z G : A) (Z' H : B)
    (α : Z' ⟶ F.obj Z) (e : F.obj G ≅ H) (h : Z ⟶ G) :
    let K := ((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧
    (DerivedCategory.singleFunctor B 0).map α ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app Z ≫
      F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map h ≫
        (derivedSingleNegOneCancelIso G).inv) ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj K) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.map (shiftedSingleFunctorIso F G H e).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso H).hom =
    (DerivedCategory.singleFunctor B 0).map (α ≫ F.map h ≫ e.hom) := by
  let f := (CochainComplex.singleFunctor A 0).map h ≫
    (shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by decide)).inv.app
      ((CochainComplex.singleFunctor A 0).obj G)
  let z := CochainComplex.HomComplex.Cocycle.equivHomShift f
  have hz : CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom = h := by
    have hc := equivHomShift_single_cancel Z G z
    dsimp only [z] at hc
    rw [AddEquiv.symm_apply_apply] at hc
    dsimp only [f] at hc
    simp only [Category.assoc, Iso.inv_hom_id_app] at hc
    erw [Category.comp_id] at hc
    exact ((CochainComplex.singleFunctor A 0).map_injective hc).symm
  have hl : DerivedCategory.Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (((CochainComplex.singleFunctor A 0).obj G)⟦(-1 : ℤ)⟧) =
      (DerivedCategory.singleFunctor A 0).map h ≫ (derivedSingleNegOneCancelIso G).inv := by
    apply (cancel_mono (derivedSingleNegOneCancelIso G).hom).mp
    have hc := localized_single_cocycle_cancel Z G z
    rw [hz] at hc
    simpa [DerivedCategory.singleFunctorIsoCompQ, Category.assoc] using hc
  simpa only [hl, hz] using derivedSourceTransport_single_cancel F Z G Z' H α e z

end Stacks.Cohomology.Corepresented
