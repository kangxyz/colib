/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensorColimits
public import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Exact sheaf tensor rows for pointwise-flat coefficients

Mono preservation and finite-colimit preservation give preservation of homology.
All acyclic complexes below are complexes of sheaves; their underlying presheaf
complexes are never assumed acyclic. This is not yet bounded-above K-flatness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory
  Sheaf.monoidalPreadditive

local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

/-- The actual sheaf tensor with a pointwise-flat coefficient preserves homology. -/
theorem smoothEtaleIntegralTensorRight_preservesHomology
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    [∀ X, Module.Flat ℤ (P.obj X)] : (tensorRight ((a).obj P)).PreservesHomology := by
  let := smoothEtaleIntegralTensorRight_preservesMonomorphisms k P
  let := smoothEtaleIntegralTensorRight_preservesFiniteColimits k P
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Every actual exact sheaf row remains exact under tensor with the flat coefficient. -/
theorem smoothEtaleIntegralTensorRight_exact
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    [∀ X, Module.Flat ℤ (P.obj X)] (T : ShortComplex S) (hT : T.Exact) :
    (T.map (tensorRight ((a).obj P))).Exact := by
  let F := tensorRight ((a).obj P)
  let := smoothEtaleIntegralTensorRight_preservesHomology k P
  rw [ShortComplex.exact_iff_isZero_homology]
  exact IsZero.of_iso (F.map_isZero
    ((ShortComplex.exact_iff_isZero_homology _).mp hT)) (T.mapHomologyIso F)

/-- Acyclicity is preserved within the sheaf category itself. -/
theorem smoothEtaleIntegralTensorRight_acyclic
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    [∀ X, Module.Flat ℤ (P.obj X)] (G : CochainComplex S ℤ) (hG : G.Acyclic) :
    (((tensorRight ((a).obj P)).mapHomologicalComplex (.up ℤ)).obj G).Acyclic := by
  intro n
  change ((G.sc n).map (tensorRight ((a).obj P))).Exact
  exact smoothEtaleIntegralTensorRight_exact k P (G.sc n) (hG n)

/-- The native row complex is the actual fixed-coefficient tensor complex. -/
def smoothEtaleIntegralRowTensorIso (G : CochainComplex S ℤ) (M : S) :
    CochainComplex.KFlatBifunctor.rowComplex (curriedTensor S) G M ≅
      ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj G :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change 𝟙 (G.X i ⊗ M) ≫ (G.d i j ▷ M) = (G.d i j ▷ M) ≫ 𝟙 (G.X j ⊗ M)
    rw [Category.id_comp, Category.comp_id])

/-- This is the acyclic-row obligation consumed by bounded-above K-flat totalization. -/
theorem smoothEtaleIntegralRow_acyclic
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    [∀ X, Module.Flat ℤ (P.obj X)] (G : CochainComplex S ℤ) (hG : G.Acyclic) :
    (CochainComplex.KFlatBifunctor.rowComplex (curriedTensor S) G ((a).obj P)).Acyclic := by
  intro n
  exact HomologicalComplex.ExactAt.of_iso
    (smoothEtaleIntegralTensorRight_acyclic k P G hG n)
    (smoothEtaleIntegralRowTensorIso k G ((a).obj P)).symm

end AlgebraicGeometry.PresheafWithTransfers
