/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.ComponentDominance

/-! # Checks for the actual source component of incidence supports -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

noncomputable section

-- Finiteness of the set of incidence components needs no global Noetherian source.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w) :
    (genericPoints (correspondenceIncidence f g h z w)).Finite :=
  finite_genericPoints_correspondenceIncidence f g h z w hw

-- The finite subtype can directly index the actual generic-coefficient cycle.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w) :
    Finite (genericPoints (correspondenceIncidence f g h z w)) :=
  (finite_genericPoints_correspondenceIncidence f g h z w hw).to_subtype

-- Equality of source images requires no admissibility or smoothness of the first support.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) =
      Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) :=
  range_integralComponent_correspondenceIncidenceLeft f g h z w hw t ht

-- The ambient source and middle schemes may both be disconnected.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X :=
  range_integralComponent_correspondenceIncidenceLeft_mem f g h z w hz hw t ht

-- Any field is allowed, without a perfectness or algebraic-closure hypothesis.
example {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
    [Smooth g]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X :=
  range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth f g h z w hz hw t ht

-- This is the exact nonverticality input for a cycle supported at generic incidence points.
-- No injectivity of the outer image map or flatness of the finite supports is assumed.
example {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
    [Smooth g]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (c : AlgebraicCycle (correspondenceIncidence f g h z w) ℤ)
    (hc : ∀ t, c t ≠ 0 → t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    ∀ t, c t ≠ 0 → Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X := by
  intro t ht
  exact range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
    f g h z w hz hw t (hc t ht)

end
