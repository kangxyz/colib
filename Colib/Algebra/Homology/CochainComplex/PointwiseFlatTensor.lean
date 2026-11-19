/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.RingTheory.Flat.Basic
public import Colib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# Exact pointwise tensor rows

Evaluation detects exactness of module-valued functors. Tensoring with a
sectionwise flat functor preserves these exact rows and hence acyclicity.
This is the single-term input to bounded-above K-flatness, not the totalization
or sequential-colimit step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w r

namespace CochainComplex.PointwiseFlatTensor

/-- Pointwise module tensor is additive on natural transformations. -/
instance (priority := 100) pointwiseModuleMonoidalPreadditive
    {C : Type u} [Category.{v} C] {R : Type r} [CommRing R] :
    MonoidalPreadditive (C ⥤ ModuleCat.{max r w} R) where
  whiskerLeft_zero := by intros; apply NatTrans.ext; funext X; simp; rfl
  zero_whiskerRight := by intros; apply NatTrans.ext; funext X; simp; rfl
  whiskerLeft_add := by intros; apply NatTrans.ext; funext X; simp; rfl
  add_whiskerRight := by intros; apply NatTrans.ext; funext X; simp; rfl

variable {C : Type u} [Category.{v} C] {R : Type r} [CommRing R]

/-- Joint evaluation detects the actual middle exactness of natural maps. -/
theorem exact_of_evaluation (S : ShortComplex (C ⥤ ModuleCat.{max r w} R))
    (hS : ∀ X, (S.map ((evaluation C (ModuleCat R)).obj X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext X
  change 𝟙 (S.homology.obj X) = 0
  exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (hS X))
    (S.mapHomologyIso ((evaluation C (ModuleCat R)).obj X)).symm).eq_of_src _ _

/-- The actual pointwise right tensor preserves every exact row. -/
theorem exact_tensorRight (M : C ⥤ ModuleCat.{max r w} R)
    [∀ X, Module.Flat R (M.obj X)] (S : ShortComplex (C ⥤ ModuleCat.{max r w} R))
    (hS : S.Exact) : (S.map (tensorRight M)).Exact := by
  apply exact_of_evaluation
  intro X
  let E := (evaluation C (ModuleCat R)).obj X
  have hSX : (S.map E).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    exact IsZero.of_iso (E.map_isZero
      ((ShortComplex.exact_iff_isZero_homology _).mp hS)) (S.mapHomologyIso E)
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact ((S.f.app X).hom.rTensor (M.obj X))
    ((S.g.app X).hom.rTensor (M.obj X))
  exact Module.Flat.rTensor_exact (M.obj X)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hSX)

/-- Tensoring an acyclic complex with an actual sectionwise flat coefficient
functor preserves acyclicity, without assuming tensor is exact globally. -/
theorem acyclic_tensorRight (M : C ⥤ ModuleCat.{max r w} R)
    [∀ X, Module.Flat R (M.obj X)] (K : CochainComplex (C ⥤ ModuleCat.{max r w} R) ℤ)
    (hK : K.Acyclic) :
    ((Functor.mapHomologicalComplex (tensorRight M) (.up ℤ)).obj K).Acyclic := by
  intro n
  change ((K.sc n).map (tensorRight M)).Exact
  exact exact_tensorRight M (K.sc n) (hK n)

/-- Sequential colimits of actual acyclic module-valued presheaf complexes
are acyclic. Exactness is obtained from module AB5 and pointwise colimits. -/
theorem acyclic_sequentialColimit
    (E : ℕ ⥤ CochainComplex (C ⥤ ModuleCat.{max r w} R) ℤ)
    (s : Cocone E) (hs : IsColimit s) (hE : ∀ i, (E.obj i).Acyclic) :
    s.pt.Acyclic := by
  let := ModuleCat.hasExactFilteredColimits.{max r w} R ℕ
  let : HasExactColimitsOfShape ℕ (C ⥤ ModuleCat.{max r w} R) := inferInstance
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let H := HomologicalComplex.homologyFunctor (C ⥤ ModuleCat.{max r w} R) (.up ℤ) n
  let := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := C ⥤ ModuleCat.{max r w} R) (J := ℕ) (.up ℤ) n
  exact IsColimit.isZero_pt (isColimitOfPreserves H hs)
    (Functor.isZero _ (fun i =>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (hE i n)))

end CochainComplex.PointwiseFlatTensor
