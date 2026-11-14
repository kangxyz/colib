/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerExtendedHomologyFactors
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomology

/-!
# Exact coefficients commute with the actual ordinary extension tail

Reuse the proved equality between the two original extension maps and
the original exact-homology/extension coherence, not a new comparison.
The composite-global-sections tail and final Ext equivalence remain to assemble.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.DerivedIndexing
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma inversePrefix {C : Type*} [Category C]
    {A B D E H : C} (e : A ≅ B) (a : B ⟶ D) (b : D ⟶ H)
    (c : A ⟶ E) (d : E ⟶ H) (h : e.hom ≫ a ≫ b = c ≫ d) :
    a ≫ b = e.inv ≫ c ≫ d := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

namespace Stacks.EtaleCohomology

/-- The existing exact-homology map commutes with the ORIGINAL extension tail for
restriction of scalars, with the existing inverse extension map identified explicitly. -/
theorem kummerExactOrdinaryTail
    (Λ : Type) [CommRing Λ] (K : CochainComplex (ModuleCat.{u + 1} Λ) ℕ) (q : ℕ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    (mapExactHomologyIso R (K.extend ComplexShape.embeddingUpNat) (q : ℤ)).hom ≫
      R.map (K.extendHomologyIso ComplexShape.embeddingUpNat (by simp :
        ComplexShape.embeddingUpNat.f q = (q : ℤ))).hom =
    (extendedHomologyTailIso R K q).hom ≫ (mapExactHomologyIso R K q).hom := by
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have h := inversePrefix
    (HomologicalComplex.homologyMapIso
      (mapExtendIso R ComplexShape.embeddingUpNat K) (q : ℤ)) _ _ _ _
    (homologyMap_mapExtendIso_hom_comp R ComplexShape.embeddingUpNat K
      (by simp : ComplexShape.embeddingUpNat.f q = (q : ℤ)))
  simpa only [HomologicalComplex.homologyMapIso_inv,
    mapExtendIso_inv_eq_derivedMapExtendIso_hom, extendedHomologyTailIso,
    Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, Category.assoc] using h

end Stacks.EtaleCohomology
end
