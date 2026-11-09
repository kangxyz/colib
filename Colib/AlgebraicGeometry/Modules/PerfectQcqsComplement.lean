/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectQcqsRoof

/-!
# Native perfect complements for restriction to a quasi-compact open

Every native perfect complex on a quasi-compact open of a qcqs scheme has a native perfect
complement whose direct sum is represented by the restriction of a native perfect complex on
the ambient scheme. The stronger derived isomorphism with the sum with the shift is retained.
No density or roof existence is assumed.

The compact localization theorem (Stacks 08EK), compact kernel generation (0A9A), and native
compact/perfect comparison (09M1) give the construction; its retract consequence is 09IQ.
-/

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty ZeroObject
open Stacks.Duality.OpenImmersion Stacks.Duality.SupportedGeneration
open Stacks.Duality.QcqsGeneration

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- A native perfect complex on a quasi-compact open, summed with its derived shift, is the
restriction of an actual native perfect complex on the ambient qcqs scheme. -/
theorem exists_isPerfectComplex_restrict_iso_biprod_shift
    (P : CochainComplex U.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P) :
    ∃ R : CochainComplex X.Modules ℤ,
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj P ⊞ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧) := by
  have : QuasiSeparatedSpace U := j.isOpenEmbedding.quasiSeparatedSpace
  have : AlgebraicGeometry.QuasiCompact j := inferInstance
  have hp : RingedSpace.IsPerfect (X := U.toRingedSpace)
      (DerivedCategory.Q.obj P) := ⟨P, hP, ⟨Iso.refl _⟩⟩
  let P' : Stacks.Duality.quasiCoherentDerivedCategory U :=
    ⟨DerivedCategory.Q.obj P,
      isQuasicoherentDerived_of_isPseudoCoherent U _ hp.isPseudoCoherent⟩
  have hPc : IsCompactObject.{u} P' := Stacks.Duality.isCompactObject_of_isPerfect P' hp
  obtain ⟨ι, K, hKc, hK0, hKdet⟩ := kernelDetected j
  let adj := restrictedDerivedRestrictAdjunction j
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward j
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward j
  obtain ⟨ι₀, G, hGc, hGgen⟩ :=
    Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X
  let G' : Option ι₀ → Stacks.Duality.quasiCoherentDerivedCategory X := fun o => o.elim 0 G
  have hG'c : ∀ o, IsCompactObject.{u} (G' o) := fun o => by
    cases o with
    | none => exact isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory X)
    | some k => exact hGc k
  have hG'gen : (ofObj G').IsWeakTriangulatedGenerator := fun F hF => hGgen F <| by
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hF ⊢
    exact fun k n g => hF (some k) n g
  obtain ⟨c, hc, ⟨e⟩⟩ :=
    exists_isCompactObject_iso_biprod_shift adj K hKc hK0 hKdet G' hG'c hG'gen P' hPc
  have hcP : RingedSpace.IsPerfect (X := X.toRingedSpace) c.obj :=
    Stacks.Duality.isPerfect_of_isCompactObject c hc
  change ∃ R : CochainComplex X.Modules ℤ,
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      Nonempty (DerivedCategory.Q.obj R ≅ c.obj) at hcP
  obtain ⟨R, hR, ⟨eR⟩⟩ := hcP
  let ιU := (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι
  have : ιU.Additive := inferInstance
  exact ⟨R, hR, ⟨((restrictFunctor j).mapDerivedCategoryFactors.app R).symm ≪≫
    (derivedRestrict j).mapIso eR ≪≫ ιU.mapIso e ≪≫ ιU.mapBiprod _ _ ≪≫
    biprod.mapIso (Iso.refl _) ((ιU.commShiftIso 1).app P')⟩⟩

/-- Every perfect complex on the open has an actual perfect complementary complex such that
their direct sum is represented by an actual global perfect restriction. -/
theorem exists_isPerfectComplex_restrict_complement_small
    (P : CochainComplex U.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P) :
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (P ⊞ C)) := by
  obtain ⟨R, hR, ⟨e⟩⟩ := exists_isPerfectComplex_restrict_iso_biprod_shift j P hP
  have hp : RingedSpace.IsPerfect (X := U.toRingedSpace)
      (DerivedCategory.Q.obj P) := ⟨P, hP, ⟨Iso.refl _⟩⟩
  have hshift := Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hp (1 : ℤ)
  change ∃ C : CochainComplex U.Modules ℤ,
    RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C ∧
      Nonempty (DerivedCategory.Q.obj C ≅ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧) at hshift
  obtain ⟨C, hC, ⟨eC⟩⟩ := hshift
  exact ⟨R, C, hR, hC, ⟨e ≪≫ biprod.mapIso (Iso.refl _) eC.symm ≪≫
    (DerivedCategory.Q.mapBiprod P C).symm⟩⟩

/-- Stacks 09IQ for an actual native perfect complex on the open and an actual native perfect
complex on the ambient scheme. -/
@[colib_tag "COL-0307",
  stacks 09IQ "Actual native perfect complex representatives of the restriction retract"]
theorem exists_isPerfectComplex_retract_restrict
    (P : CochainComplex U.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P) :
    ∃ R : CochainComplex X.Modules ℤ,
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      Nonempty (Retract (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R))) := by
  obtain ⟨R, hR, ⟨e⟩⟩ := exists_isPerfectComplex_restrict_iso_biprod_shift j P hP
  exact ⟨R, hR, ⟨⟨biprod.inl ≫ e.inv, e.hom ≫ biprod.fst, by simp⟩⟩⟩

section AnyModel

universe d

/-- The actual native perfect complementary complexes and their restriction isomorphism,
in an arbitrary chosen derived-category model on the open. -/
@[colib_tag "COL-0307"]
theorem exists_isPerfectComplex_restrict_complement
    [h : HasDerivedCategory.{d} U.Modules]
    (P : CochainComplex U.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P) :
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (P ⊞ C)) := by
  obtain ⟨R, C, hR, hC, he⟩ := exists_isPerfectComplex_restrict_complement_small j P hP
  refine ⟨R, C, hR, hC, ?_⟩
  apply (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).1
  let := Scheme.Modules.hasDerivedCategory U
  exact (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2 he

end AnyModel

end AlgebraicGeometry.Scheme.Modules
