/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.CechSectionsComplex
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardAffineOverlapLaurent
public import Mathlib.Algebra.MonoidAlgebra.Module
public import StacksFrontier.AlgebraicGeometry.Modules.SectionsTransportAlongIso
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Projective coefficient modules on the standard charts of the projective line -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) (M : (line R).Modules)
  [M.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]

private theorem projective_restrictScalars {A : Type u} [CommRing A] [Algebra R A]
    [Module.Free R A] (P : ModuleCat.{u} A) [Module.Projective A P] :
    Module.Projective R ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj P) := by
  let Q := (ModuleCat.restrictScalars.{u} (algebraMap R A)).obj P
  let : Module A Q := P.isModule
  let : IsScalarTower R A Q := ⟨fun r a q ↦ by
    change (r • a) • q = (algebraMap R A r) • a • q
    rw [Algebra.smul_def, mul_smul]⟩
  let : Module.Projective A Q := inferInstanceAs (Module.Projective A P)
  obtain ⟨i, hi⟩ := Module.projective_def.mp (show Module.Projective A Q from inferInstance)
  let q : (Q →₀ A) →ₗ[A] Q := Finsupp.linearCombination A id
  exact Module.Projective.of_split (i.restrictScalars R) (q.restrictScalars R)
    (by ext x; exact hi x)

private theorem projective_globalSectionsOver_spec {A : Type u} [CommRing A] [Algebra R A]
    [Module.Free R A] (N : (Spec (.of A)).Modules) [N.IsQuasicoherent]
    (hN : Scheme.Modules.IsFiniteLocallyFree N) :
    Module.Projective R ((globalSectionsOver
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj N) := by
  let G := moduleSpecΓFunctor (R := .of A)
  let : Module.Projective A (G.obj N) :=
    (moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree N hN).2
  let P := (ModuleCat.restrictScalars.{u} (algebraMap R A)).obj (G.obj N)
  let : Module.Projective R P :=
    projective_restrictScalars R (G.obj N)
  have e : P ≅ (globalSectionsOver (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj N := by
    refine (ModuleCat.restrictScalars (algebraMap R A)).mapIso
      ((moduleSpecΓIsoGlobalSectionsOver (.of A)).app N) ≪≫ ?_
    let idA : Spec (.of A) ⟶ Spec (.of A) := 𝟙 _
    exact (ModuleCat.restrictScalarsComp'App (algebraMap R A)
      ((Scheme.ΓSpecIso (.of A)).inv ≫ idA.appTop).hom
      ((Scheme.ΓSpecIso R).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop).hom
      (by
        let h : R ⟶ .of A := CommRingCat.ofHom (algebraMap R A)
        simp only [idA, Scheme.Hom.id_appTop, Category.comp_id]
        exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality h).symm)
      ((SheafOfModules.evaluation (Spec (.of A)).ringCatSheaf (.op ⊤)).obj N)).symm
  exact Module.Projective.of_equiv e.toLinearEquiv

/-- The sections of a vector bundle over either standard chart are projective as modules over
the coefficient ring. -/
theorem projective_standardChartSections (i : Fin 2) :
    Module.Projective R ((globalSectionsOver (lineProjection R)).obj
      ((restrictPushMod (standardChart 1 (Spec R) i)).obj M)) := by
  let U := standardChart 1 (Spec R) i
  let σ := ULift.{u} {j : Fin 2 // j ≠ i}
  let q := (AffineSpace.SpecIso σ R).symm ≪≫
    standardChartIso 1 i (Equiv.ulift : σ ≃ {j : Fin 2 // j ≠ i}) (Spec R)
  let j := q.hom ≫ U.ι
  have hj : j ≫ lineProjection R =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)) := by
    dsimp [j, q, U]
    rw [Category.assoc, Category.assoc]
    change (AffineSpace.SpecIso σ R).inv ≫ (standardChartIso 1 i Equiv.ulift (Spec R)).hom ≫
      (standardChart 1 (Spec R) i).ι ≫ (projectiveSpaceOver 1 (Spec R) ↘ Spec R) = _
    rw [standardChartIso_hom_ι_over, AffineSpace.SpecIso_inv_over]
  let N := M.restrict j
  let : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j M
  have hN : Scheme.Modules.IsFiniteLocallyFree N :=
    Scheme.Modules.IsFiniteLocallyFree.restrict j
      ((Scheme.Modules.isFiniteLocallyFree_iff M).2 inferInstance)
  have hP : Module.Projective R ((globalSectionsOver
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)))).obj N) :=
    projective_globalSectionsOver_spec R (A := MvPolynomial σ R) N hN
  -- Transport first along the actual chart identification, then along its open inclusion.
  let e : ((globalSectionsOver (lineProjection R)).obj ((restrictPushMod U).obj M)) ≅
      (globalSectionsOver (j ≫ lineProjection R)).obj N := by
    let e₁ := (globalSectionsOverPushforwardNatIso U.ι (lineProjection R)
      (U.ι ≫ lineProjection R) rfl).app (M.restrict U.ι)
    let e₂ := globalSectionsOverPullbackIso q (U.ι ≫ lineProjection R) (j ≫ lineProjection R)
      (Category.assoc _ _ _).symm
      ((Scheme.Modules.restrictFunctorIsoPullback q.hom).symm.app _ ≪≫
        (Scheme.Modules.restrictFunctorComp q.hom U.ι).symm.app M)
    exact e₁ ≪≫ e₂
  rw [hj] at e
  let := hP
  exact Module.Projective.of_equiv e.symm.toLinearEquiv

/-- The sections of a vector bundle over the actual overlap are projective over the
coefficient ring. -/
theorem projective_standardOverlapSections :
    Module.Projective R ((globalSectionsOver (lineProjection R)).obj
      ((restrictPushMod (lineChartZero R ⊓ lineChartOne R)).obj M)) := by
  let U := lineChartZero R ⊓ lineChartOne R
  let q := standardOverlapLaurentIso R
  let j := q.hom ≫ U.ι
  let N := M.restrict j
  let : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j M
  let : Module.Free R (LaurentPolynomial R) :=
    Module.Free.of_basis ((Finsupp.basisSingleOne (R := R) (ι := ℤ)).map
      (AddMonoidAlgebra.coeffLinearEquiv R).symm)
  have hN : Scheme.Modules.IsFiniteLocallyFree N :=
    Scheme.Modules.IsFiniteLocallyFree.restrict j
      ((Scheme.Modules.isFiniteLocallyFree_iff M).2 inferInstance)
  have hP : Module.Projective R ((globalSectionsOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))))).obj N) :=
    projective_globalSectionsOver_spec R N hN
  let e : ((globalSectionsOver (lineProjection R)).obj ((restrictPushMod U).obj M)) ≅
      (globalSectionsOver (j ≫ lineProjection R)).obj N := by
    let e₁ := (globalSectionsOverPushforwardNatIso U.ι (lineProjection R)
      (U.ι ≫ lineProjection R) rfl).app (M.restrict U.ι)
    let e₂ := globalSectionsOverPullbackIso q (U.ι ≫ lineProjection R) (j ≫ lineProjection R)
      (Category.assoc _ _ _).symm
      ((Scheme.Modules.restrictFunctorIsoPullback q.hom).symm.app _ ≪≫
        (Scheme.Modules.restrictFunctorComp q.hom U.ι).symm.app M)
    exact e₁ ≪≫ e₂
  have hj : j ≫ lineProjection R =
      Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))) :=
    (Category.assoc _ _ _).trans (standardOverlapLaurentIso_over R)
  rw [hj] at e
  let := hP
  exact Module.Projective.of_equiv e.symm.toLinearEquiv

end AlgebraicGeometry.projectiveSpaceOver
