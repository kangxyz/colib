/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Colib.Topology.DoubleMappingCylinder.WeakInvariance

/-!
# Complete weak equivalence of actual reduced cone maps

A strictly commuting based square whose two original sides are complete weak equivalences induces
a complete weak equivalence of the unchanged reduced cone quotients, provided all four actual
points have HEP inclusions. The proof first uses weak invariance of ordinary double cylinders and
then the genuine reduction homotopy equivalences. It never chooses a weak-map inverse.
-/
@[expose] public section
noncomputable section

open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Topology.ReducedMappingCone

variable {X Y X' Y' : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)
  (x₀' : X') (y₀' : Y') (f' : C(X', Y')) (hf' : f' x₀' = y₀')
  (a : C(X, X')) (b : C(Y, Y')) (ha : a x₀ = x₀') (hb : b y₀ = y₀')
  (comm : ∀ x, b (f x) = f' (a x))

include hf hf' in
/-- Complete weak side equivalences preserve the original reduced cone map when the actual
four basepoints are well-based. No stable exactness or separation shortcut is used. -/
@[colib_ref "quillen"
  "Quillen/Topology/HomotopyCofiber/ReducedMappingConeWeakEquivalence.lean:39-103"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem map_isWeakHomotopyEquivalence
    (hX : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀)))
    (hX' : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀')))
    (hY' : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀')))
    (haWeak : IsWeakHomotopyEquivalence a) (hbWeak : IsWeakHomotopyEquivalence b) :
    IsWeakHomotopyEquivalence (map x₀ y₀ f x₀' y₀' f' a b ha hb comm) := by
  have wf : TopCat.ofHom f ≫ TopCat.ofHom b = TopCat.ofHom a ≫ TopCat.ofHom f' := by
    ext x
    exact comm x
  have wg : TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) ≫ 𝟙 _ =
      TopCat.ofHom a ≫ TopCat.ofHom (ContinuousMap.const X' (PUnit.unit : PUnit.{u + 1})) := rfl
  let m := DoubleCylinder.map (unreducedSquare f) (unreducedSquare f')
    (TopCat.ofHom a) (TopCat.ofHom b) (𝟙 _) wf wg
  have hm : IsWeakHomotopyEquivalence m.hom :=
    DoubleCylinder.map_isWeakHomotopyEquivalence (unreducedSquare f) (unreducedSquare f')
      (TopCat.ofHom a) (TopCat.ofHom b) (𝟙 _) wf wg haWeak hbWeak
      (isWeakHomotopyEquivalence_id PUnit.{u + 1})
  have hw : reduction x₀ y₀ f ≫ TopCat.ofHom (map x₀ y₀ f x₀' y₀' f' a b ha hb comm) =
      m ≫ reduction x₀' y₀' f' := by
    apply (unreducedSquare f).hom_ext
    · ext ⟨x, t⟩
      change map x₀ y₀ f x₀' y₀' f' a b ha hb comm
          (reduction x₀ y₀ f (unreducedCylinder f (x, t))) =
        reduction x₀' y₀' f' (m (unreducedCylinder f (x, t)))
      rw [reduction_cylinder]
      rw [show m (unreducedCylinder f (x, t)) = unreducedCylinder f' (a x, t) from
        DoubleCylinder.map_cylinder_apply (unreducedSquare f) (unreducedSquare f')
          (TopCat.ofHom a) (TopCat.ofHom b) (𝟙 _) wf wg x t]
      rw [reduction_cylinder]
      rfl
    · ext z
      cases z with
      | inl y =>
        change map x₀ y₀ f x₀' y₀' f' a b ha hb comm
            (reduction x₀ y₀ f (unreducedEnd f (Sum.inl y))) =
          reduction x₀' y₀' f' (m (unreducedEnd f (Sum.inl y)))
        rw [reduction_end]
        rw [show m (unreducedEnd f (Sum.inl y)) = unreducedEnd f' (Sum.inl (b y)) from
          DoubleCylinder.map_left (unreducedSquare f) (unreducedSquare f')
            (TopCat.ofHom a) (TopCat.ofHom b) (𝟙 _) wf wg y]
        rw [reduction_end]
        rfl
      | inr z =>
        change map x₀ y₀ f x₀' y₀' f' a b ha hb comm
            (reduction x₀ y₀ f (unreducedEnd f (Sum.inr z))) =
          reduction x₀' y₀' f' (m (unreducedEnd f (Sum.inr z)))
        rw [reduction_end]
        rw [show m (unreducedEnd f (Sum.inr z)) = unreducedEnd f' (Sum.inr z) from
          DoubleCylinder.map_right (unreducedSquare f) (unreducedSquare f')
            (TopCat.ofHom a) (TopCat.ofHom b) (𝟙 _) wf wg z]
        rw [reduction_end]
        exact map_point x₀ y₀ f x₀' y₀' f' a b ha hb comm
  have hs := isWeakHomotopyEquivalence_of_homotopyEquiv
    (reductionHomotopyEquiv x₀ y₀ f hf hX hY)
  have ht := isWeakHomotopyEquivalence_of_homotopyEquiv
    (reductionHomotopyEquiv x₀' y₀' f' hf' hX' hY')
  have h := ht.comp hm
  change IsWeakHomotopyEquivalence ((m ≫ reduction x₀' y₀' f').hom) at h
  rw [← hw] at h
  exact h.of_comp_left hs

end Topology.ReducedMappingCone
