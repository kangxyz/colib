/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Limits.SeparableRationalMarkedChart
/-! # The original ground-field structure on an actual finite integral chart -/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory IntermediateField AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
/-- Use the native subalgebra scalar structure at the finite intermediate field. -/
local instance integralChartGroundAlgebra (E L : Type u) [Field E] [Field L]
    [Algebra E L] (t : Finset L) : Algebra E (adjoin E (t : Set L)) :=
  (adjoin E (t : Set L)).toSubalgebra.algebra

/-- The actual localized tensor chart is smooth over its finite coefficient field. -/
theorem finiteIntegralChart_smooth_coefficient (E L B : Type u) [Field E] [Field L]
    [Algebra E L]
    [CommRing B] [Algebra E B] [Algebra.Smooth E B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B) :
    Algebra.Smooth (adjoin E (t : Set L)) (Localization.Away e) := by
  let A := adjoin E (t : Set L)
  let T := A ⊗[E] B
  let : Algebra.Smooth A T := inferInstance
  let : Algebra.Etale T (Localization.Away e) := Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Smooth.comp A T (Localization.Away e)

/-- The same chart remains smooth over the original ground field, and its actual
etale map to the original affine scheme preserves that ground-field structure. -/
theorem finiteIntegralChart_smooth_ground_and_square (K E L B : Type u)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Algebra.IsSeparable E L]
    [CommRing B] [Algebra E B] [Algebra K B] [IsScalarTower K E B]
    [Algebra.Smooth E B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B) :
    let C := Localization.Away e
    Algebra.Smooth K C ∧
      (Scheme.finsetLocalizationToBase E L B t e ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) =
        Spec.map (CommRingCat.ofHom (algebraMap K C))) := by
  let A := adjoin E (t : Set L)
  let T := A ⊗[E] B
  let C := Localization.Away e
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let : Algebra.FinitePresentation K E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth K E := {}
  let : Algebra.Smooth K B := Algebra.Smooth.comp K E B
  let : Module.Finite E A := finite_finsetAdjoinDiagram_obj E L t
  let : Algebra.FormallyEtale E A := Algebra.FormallyEtale.of_isSeparable E A
  let : Algebra.FinitePresentation E A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth E A := {}
  let : Algebra.Smooth E T := Algebra.Smooth.comp E A T
  let : Algebra.Etale T C := Algebra.Etale.of_isLocalizationAway e
  let : Algebra.Smooth E C := Algebra.Smooth.comp E T C
  refine ⟨Algebra.Smooth.comp K E C, ?_⟩
  simp only [Scheme.finsetLocalizationToBase, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [IsScalarTower.algebraMap_apply K E B]
  rw [AlgHom.commutes]
  rw [← IsScalarTower.algebraMap_apply E
    ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e)]
  exact (IsScalarTower.algebraMap_apply K E (Localization.Away e) x).symm

end AlgebraicGeometry.Scheme
