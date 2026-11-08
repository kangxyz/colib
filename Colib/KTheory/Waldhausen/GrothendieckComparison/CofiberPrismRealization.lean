/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.CofiberPrismFaces
public import Colib.KTheory.Waldhausen.Basic
public import Colib.KTheory.Waldhausen.BisimplexRealization

/-! # The actual continuous cofiber prism and its original weak-arrow faces

The exact cofiber grid is realized as a continuous triangle-times-interval family. Its
boundary squares remain the three specified original weak-arrow simplices.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/CofiberPrismRealization.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The continuous original triangle with an independent nerve interval coordinate. -/
def cofiberPrismRealization :
    C(StdSimplex ℝ (Fin 3) × unitInterval, W.Delooping) :=
  (bisimplexRealization W (cofiberTwoPrism W i q hi hwi hQ)
      (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ)).comp
    ⟨fun p ↦ (p.1, StdSimplex.homeomorphI.symm p.2), by fun_prop⟩

/-- The full original inverse product-simplex realization retains both coordinates. -/
theorem cofiberPrismRealization_apply (z : StdSimplex ℝ (Fin 3)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z, t) =
      bisimplexRealization W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ)
        (z, StdSimplex.homeomorphI.symm t) := rfl

/-- The source boundary is the entire original identity weak-arrow square. -/
theorem cofiberPrismRealization_source_face
    (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 2), t) =
      bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
        (z, StdSimplex.homeomorphI.symm t) := by
  have h := bisimplexRealization_precomp W (cofiberTwoPrism W i q hi hwi hQ)
    (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) (SimplexCategory.δ 2) (𝟙 ⦋1⦌)
    z (StdSimplex.homeomorphI.symm t)
  have he := bisimplexRealization_congr W _
    ((cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ).precomp W.cof W.weq
      (SimplexCategory.δ 2) (𝟙 ⦋1⦌))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
    (W.cofiberTwoPrism_source_face i q hi hwi hQ)
  rw [he] at h
  rw [cofiberPrismRealization_apply]
  simpa using h

/-- The middle boundary is the entire original weak-cofibration square. -/
theorem cofiberPrismRealization_middle_face
    (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 1), t) =
      bisimplexRealization W (W.weakObjectSimplex i hwi).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex i hwi).property)
        (z, StdSimplex.homeomorphI.symm t) := by
  have h := bisimplexRealization_precomp W (cofiberTwoPrism W i q hi hwi hQ)
    (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) (SimplexCategory.δ 1) (𝟙 ⦋1⦌)
    z (StdSimplex.homeomorphI.symm t)
  have he := bisimplexRealization_congr W _
    ((cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ).precomp W.cof W.weq
      (SimplexCategory.δ 1) (𝟙 ⦋1⦌))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex i hwi).property)
    (W.cofiberTwoPrism_middle_face i q hi hwi hQ)
  rw [he] at h
  rw [cofiberPrismRealization_apply]
  simpa using h

/-- The quotient boundary is the entire original zero-to-quotient weak-arrow square. -/
theorem cofiberPrismRealization_quotient_face
    (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 0), t) =
      bisimplexRealization W (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).property)
        (z, StdSimplex.homeomorphI.symm t) := by
  have h := bisimplexRealization_precomp W (cofiberTwoPrism W i q hi hwi hQ)
    (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) (SimplexCategory.δ 0) (𝟙 ⦋1⦌)
    z (StdSimplex.homeomorphI.symm t)
  have he := bisimplexRealization_congr W _
    ((cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ).precomp W.cof W.weq
      (SimplexCategory.δ 0) (𝟙 ⦋1⦌))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).property)
    (W.cofiberTwoPrism_quotient_face i q hi hwi hQ)
  rw [he] at h
  rw [cofiberPrismRealization_apply]
  simpa using h

end CategoryTheory.Waldhausen.Structure
