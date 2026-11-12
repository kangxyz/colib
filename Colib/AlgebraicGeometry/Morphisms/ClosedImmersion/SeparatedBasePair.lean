/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Closed pairs over a separated base -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A Cartesian pair over a separated intermediate scheme is a closed
subscheme of the product over the original base. -/
theorem isClosedImmersion_pullbackLift_of_separated_base
    {D X Y B S : Scheme.{u}} (r : D ⟶ X) (s : D ⟶ Y)
    (f : X ⟶ B) (g : Y ⟶ B) (H : IsPullback r s f g)
    (p : B ⟶ S) [IsSeparated p] (u : X ⟶ S) (v : Y ⟶ S)
    (hu : f ≫ p = u) (hv : g ≫ p = v) (h : r ≫ u = s ≫ v) :
    IsClosedImmersion (pullback.lift r s h) := by
  let e := H.isoPullback
  let d := pullback.mapDesc f g p
  let c := pullback.congrHom hu hv
  let : IsClosedImmersion (e.hom ≫ d ≫ c.hom) := inferInstance
  have he : e.hom ≫ d ≫ c.hom = pullback.lift r s h := by
    apply pullback.hom_ext
    · simp [e, d, c, pullback.map, Category.assoc]
    · simp [e, d, c, pullback.map, Category.assoc]
  exact he ▸ (inferInstance : IsClosedImmersion (e.hom ≫ d ≫ c.hom))

end AlgebraicGeometry.Scheme
