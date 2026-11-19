/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.PointwiseFlatTensor
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# K-flatness for the actual pointwise tensor total

The single-row total comparison and bounded-above truncation-colimit argument
are the existing native K-flat API. Their exactness inputs are discharged by
pointwise flatness and exact sequential colimits, not taken as new hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w r

namespace CochainComplex.PointwiseFlatTensor

variable {C : Type u} [Category.{v} C] {R : Type r} [CommRing R]

/-- The explicit native tensor row is the actual pointwise right-tensor complex. -/
def rowTensorIso (G : CochainComplex (C ⥤ ModuleCat.{max r w} R) ℤ)
    (M : C ⥤ ModuleCat.{max r w} R) :
    KFlatBifunctor.rowComplex (curriedTensor (C ⥤ ModuleCat.{max r w} R)) G M ≅
      (Functor.mapHomologicalComplex (tensorRight M) (.up ℤ)).obj G :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change 𝟙 (G.X i ⊗ M) ≫ (G.d i j ▷ M) = (G.d i j ▷ M) ≫ 𝟙 (G.X j ⊗ M)
    rw [Category.id_comp, Category.comp_id])

/-- A sectionwise flat functor in a single degree is K-flat for the native total. -/
theorem kFlat_single (M : C ⥤ ModuleCat.{max r w} R) [∀ X, Module.Flat R (M.obj X)] (n : ℤ) :
    KFlatBifunctor.KFlat (curriedTensor (C ⥤ ModuleCat.{max r w} R))
      ((HomologicalComplex.single (C ⥤ ModuleCat.{max r w} R) (.up ℤ) n).obj M) := by
  apply KFlatBifunctor.kFlat_single_of_exact (curriedTensor (C ⥤ ModuleCat.{max r w} R)) M n
  intro G hG i
  exact HomologicalComplex.ExactAt.of_iso
    (acyclic_tensorRight M G hG i) (rowTensorIso G M).symm

/-- The native signed total with a bounded-above, termwise section-flat complex
preserves acyclicity in its other variable. -/
theorem kFlat_of_boundedAbove (K : CochainComplex (C ⥤ ModuleCat.{max r w} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b]
    [∀ n X, Module.Flat R ((K.X n).obj X)] :
    KFlatBifunctor.KFlat (curriedTensor (C ⥤ ModuleCat.{max r w} R)) K := by
  let : ∀ L : HomologicalComplex₂ (C ⥤ ModuleCat.{max r w} R) (.up ℤ) (.up ℤ), L.HasTotal (.up ℤ) :=
    fun _ => inferInstance
  apply KFlatBifunctor.kFlat_of_isStrictlyLE (curriedTensor (C ⥤ ModuleCat.{max r w} R)) K b
  · intro M
    apply preservesColimitsOfShape_of_evaluation
    intro X
    change PreservesColimitsOfShape ℕ
      (((evaluation C (ModuleCat.{max r w} R)).obj X) ⋙ tensorLeft (M.obj X))
    infer_instance
  · exact acyclic_sequentialColimit
  · intro n
    exact kFlat_single (K.X n) n

end CochainComplex.PointwiseFlatTensor
