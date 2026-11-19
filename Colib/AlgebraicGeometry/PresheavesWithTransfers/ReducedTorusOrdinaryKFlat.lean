/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryTermFlat
public import Colib.Algebra.Homology.CochainComplex.PointwiseKFlat

/-! # K-flatness of the original ordinary integral reduced-torus cochains

The complex is the native nonpositive extension of alternating simplex chains.
No replacement complex or derived-tensor comparison is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
  AlgebraicTopology AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- Retained simplex terms are flat; positive-degree terms are genuinely zero. -/
instance reducedTorusOrdinaryIntegralCochains_sections_flat (q : ℕ) (n : ℤ)
    (X : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ) :
    Module.Flat ℤ (((reducedTorusOrdinaryIntegralCochains k q).X n).obj X) := by
  by_cases hn : n ≤ 0
  · have he : -(((-n).toNat : ℕ) : ℤ) = n := by omega
    rw [← he]
    exact reducedTorusOrdinaryIntegralCochains_sections_flat_neg k q (-n).toNat X
  · have hz := ((CategoryTheory.evaluation _ (ModuleCat ℤ)).obj X).map_isZero
      (reducedTorusOrdinaryIntegralCochains_isZero_X k q n (by omega))
    let : Subsingleton (((reducedTorusOrdinaryIntegralCochains k q).X n).obj X) :=
      ModuleCat.subsingleton_of_isZero hz
    rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
    intro A B _ _ _ _ f hf x y hxy
    exact Subsingleton.elim _ _

/-- The native signed tensor total with the original complex preserves acyclicity. -/
theorem reducedTorusOrdinaryIntegralCochains_kFlat (q : ℕ) :
    CochainComplex.KFlatBifunctor.KFlat
      (curriedTensor ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ))
      (reducedTorusOrdinaryIntegralCochains k q) :=
  CochainComplex.PointwiseFlatTensor.kFlat_of_boundedAbove
    (reducedTorusOrdinaryIntegralCochains k q) 0

end AlgebraicGeometry.PresheafWithTransfers
