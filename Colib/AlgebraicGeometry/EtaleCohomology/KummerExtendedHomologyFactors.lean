/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerExactHomologyFactors

/-!
# Existing extended homology expressed through its actual homotopy factors

Identify the original derivedHomologyObjIso and extendedHomologyIso with
actual homologyFunctorFactorsh and ordinary tails. No final Ext equality is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology
section General
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
variable [HasDerivedCategory B]

/-- The original derived-category homology reading, not a substitute iso, factors
through the actual homotopy-category homology comparison. -/
theorem kummerDerivedHomologyObj_factors (Z : CochainComplex B ℤ) (q : ℤ) :
    (derivedHomologyObjIso Z q).hom =
      (DerivedCategory.homologyFunctorFactorsh B q).hom.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj Z) ≫
      (HomotopyCategory.homologyFunctorFactors B (.up ℤ) q).hom.app Z ≫
      (homologyFunctorObjIso Z q).hom := by
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp only [derivedHomologyObjIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc]

/-- This tail retains the actual homotopy-to-complex comparison and actual extension
comparison. It is not defined to be the full desired coefficient comparison. -/
def kummerOrdinaryExtendedTail (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℕ) (q : ℕ) :=
  (HomotopyCategory.homologyFunctorFactors B (.up ℤ) (q : ℤ)).hom.app
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)) ≫
  (homologyFunctorObjIso
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))
      (q : ℤ)).hom ≫
  (extendedHomologyTailIso F K q).hom

/-- The actual original extended homology iso begins with precisely the factorsh
that appears in the verified exact-derived coefficient coherence. -/
theorem kummerExtendedHomology_factors (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℕ) (q : ℕ) :
    (extendedHomologyIso F K q).hom =
      (DerivedCategory.homologyFunctorFactorsh B (q : ℤ)).hom.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))) ≫
      kummerOrdinaryExtendedTail F K q := by
  rw [extendedHomologyIso_hom_eq, kummerDerivedHomologyObj_factors]
  simp only [kummerOrdinaryExtendedTail, Category.assoc]

end General
end Stacks.EtaleCohomology
end
