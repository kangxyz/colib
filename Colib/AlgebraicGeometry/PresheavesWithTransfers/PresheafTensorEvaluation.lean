/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusPresheafAW
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Evaluation of the chosen antidiagonal tensor coproduct

Only the degreewise isomorphism and its exact inclusion
equation are established here. Differential compatibility remains a subsequent
proof, not a parameter or a claimed consequence.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))
variable (K L : ChainComplex
  ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) ℕ)

/-- The literal chosen antidiagonal summand family of the native tensor total. -/
def presheafTensorAntidiagonal (n : ℕ) :
    {ij : ℕ × ℕ // ij.1 + ij.2 = n} →
      ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) :=
  fun ij => K.X ij.1.1 ⊗ L.X ij.1.2

/-- Evaluation preserves this actual chosen coproduct; the comparison is
canonical and has the native tensor total as both endpoint models. -/
def presheafTensorEvaluationXIso (n : ℕ) :
    ((HomologicalComplex.tensorObj K L).X n).obj (op U) ≅
    (HomologicalComplex.tensorObj
      ((((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K)
      ((((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj L)).X n :=
  (asIso (sigmaComparison
    ((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
      (ModuleCat.{u + 1} ℤ)).obj (op U))
    (presheafTensorAntidiagonal k K L n))).symm

/-- The comparison sends each evaluated native summand inclusion to the
corresponding native inclusion, without reindexing or changing the sign. -/
theorem presheafTensorEvaluationXIso_ι (p q n : ℕ) (h : p + q = n) :
    (HomologicalComplex.ιTensorObj K L p q n h).app (op U) ≫
      (presheafTensorEvaluationXIso k U K L n).hom =
    HomologicalComplex.ιTensorObj
      ((((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K)
      ((((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj L) p q n h := by
  exact map_ι_comp_inv_sigmaComparison
    ((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
      (ModuleCat.{u + 1} ℤ)).obj (op U))
    (presheafTensorAntidiagonal k K L n) ⟨(p, q), h⟩

end AlgebraicGeometry.PresheafWithTransfers
