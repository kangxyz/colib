/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerTermwiseSourceNormalization

/-!
# Extended homology for the actual coefficient natural transformation

Naturality in the additive functor, followed by specialization to the
original coefficient comparison. Exact-derived homology/factorsh coherence and the
final Ext comparison remain separate obligations.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology
section General
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
variable {F G : A ⥤ B} [F.Additive] [G.Additive] (τ : F ⟶ G)

private theorem extendXCoefficientNaturality (K : CochainComplex A ℕ) (o : Option ℕ) :
    τ.app (HomologicalComplex.extend.X K o) ≫ (derivedMapExtendXIso G K o).hom =
    (derivedMapExtendXIso F K o).hom ≫
      HomologicalComplex.extend.mapX ((τ.mapHomologicalComplex (.up ℕ)).app K) o := by
  cases o with
  | none => exact (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl)).eq_of_src _ _
  | some k =>
    dsimp [derivedMapExtendXIso, HomologicalComplex.extend.mapX, HomologicalComplex.extend.X]
    simp

/-- The existing extension-by-zero comparison is natural in the additive functor. -/
theorem kummerDerivedMapExtend_coefficient (K : CochainComplex A ℕ) :
    (τ.mapHomologicalComplex (.up ℤ)).app (K.extend ComplexShape.embeddingUpNat) ≫
      (derivedMapExtendIso G ComplexShape.embeddingUpNat K).hom =
    (derivedMapExtendIso F ComplexShape.embeddingUpNat K).hom ≫
      HomologicalComplex.extendMap ((τ.mapHomologicalComplex (.up ℕ)).app K)
        ComplexShape.embeddingUpNat := by
  ext j
  exact extendXCoefficientNaturality τ K (ComplexShape.embeddingUpNat.r j)

/-- The existing ordinary homology tail respects the actual coefficient transformation. -/
theorem kummerExtendedHomologyTail_coefficient (K : CochainComplex A ℕ) (q : ℕ) :
    HomologicalComplex.homologyMap
      ((τ.mapHomologicalComplex (.up ℤ)).app (K.extend ComplexShape.embeddingUpNat))
      (q : ℤ) ≫ (extendedHomologyTailIso G K q).hom =
    (extendedHomologyTailIso F K q).hom ≫
      HomologicalComplex.homologyMap ((τ.mapHomologicalComplex (.up ℕ)).app K) q := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f (q : ℤ))
    (kummerDerivedMapExtend_coefficient τ K)
  simp only [HomologicalComplex.homologyMap_comp] at h
  simp only [extendedHomologyTailIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom]
  rw [reassoc_of% h, HomologicalComplex.extendHomologyIso_hom_naturality,
    ← Category.assoc]

/-- The original derived-to-ordinary extended homology iso is natural in coefficients. -/
theorem kummerExtendedHomology_coefficient [HasDerivedCategory B]
    (K : CochainComplex A ℕ) (q : ℕ) :
    (DerivedCategory.homologyFunctor B (q : ℤ)).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map
        ((τ.mapHomologicalComplex (.up ℤ)).app (K.extend ComplexShape.embeddingUpNat)))) ≫
      (extendedHomologyIso G K q).hom =
    (extendedHomologyIso F K q).hom ≫
      HomologicalComplex.homologyMap ((τ.mapHomologicalComplex (.up ℕ)).app K) q := by
  rw [extendedHomologyIso_hom_eq, extendedHomologyIso_hom_eq,
    ← Category.assoc, derivedHomologyObjIso_hom_naturality, Category.assoc,
    kummerExtendedHomologyTail_coefficient, Category.assoc]
end General

/-- Specialize to the ORIGINAL étale coefficient comparison, not a replacement map. -/
theorem kummerOriginalCoefficient_extendedHomology
    (Λ : Type) [CommRing Λ] (X : Scheme.{u})
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let τ := (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom
    let K := (injectiveResolution M).cocomplex
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((τ.mapHomologicalComplex (.up ℤ)).app (K.extend ComplexShape.embeddingUpNat)))) ≫
      (extendedHomologyIso
        (etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙
          etaleModuleGlobalSections.{u, 0} ℤ X) K q).hom =
    (extendedHomologyIso
      (etaleModuleGlobalSections.{u, 0} Λ X ⋙
        ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) K q).hom ≫
      HomologicalComplex.homologyMap ((τ.mapHomologicalComplex (.up ℕ)).app K) q := by
  exact kummerExtendedHomology_coefficient _ _ _

end Stacks.EtaleCohomology
end
