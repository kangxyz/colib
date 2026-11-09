/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition

/-!
# Actual graph postcomposition pushforward regressions

The target morphism is arbitrary, while the literal support map is proved finite.
Tests retain actual generic images, residue degrees, signed cycles, empty middle
schemes, and compact middle graph support.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] isIntegral_integralComponentAt

universe u

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) (z : pullback (C := Scheme) f g)

example [IsSeparated h] (hz : IsFiniteCorrespondencePoint f g z) :
    IsFinite (correspondenceGraphPostcompositionMap f g h ψ hψ z) :=
  isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz

example : correspondenceGraphPostcompositionMap f g h ψ hψ z ≫ pullback.fst f h =
    (integralComponentAt z).subschemeι ≫ pullback.fst f g :=
  correspondenceGraphPostcompositionMap_fst f g h ψ hψ z

example [IsSeparated h] [LocallyOfFiniteType h]
    (hz : IsFiniteCorrespondencePoint f g z) :
    IsFiniteCorrespondencePoint f h
      (correspondenceGraphPostcompositionMap f g h ψ hψ z
        (genericPoint (integralComponentAt z).subscheme)) :=
  isFiniteCorrespondencePoint_graphPostcomposition_genericPoint f g h ψ hψ z hz

end Geometry

section Smooth

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

open Classical in
example (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
    (t : genericPoints Y)
    (ht : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {t.val}) :
    (incidenceTorCorrespondence f g h z (correspondenceGraphMap g h ψ hψ t.val)
      hz (isFiniteCorrespondencePoint_graphMap g h ψ hψ t)).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
      finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
        (single (genericPoint (integralComponentAt z).subscheme) 1) :=
  incidenceTorCorrespondence_graph_right_val_of_range_subset f g h ψ hψ z hz t ht

open Classical in
example (hY : (genericPoints Y).Finite)
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g h ψ hψ hY)).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
      finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
        (single (genericPoint (integralComponentAt z).subscheme) 1) :=
  incidenceTorPairing_single_graph_right_val f g h ψ hψ hY z hz

example (hY : (genericPoints Y).Finite)
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g h ψ hψ hY) =
      singleFiniteCorrespondence f h
        (correspondenceGraphPostcompositionMap f g h ψ hψ z
          (genericPoint (integralComponentAt z).subscheme))
        (isFiniteCorrespondencePoint_graphPostcomposition_genericPoint f g h ψ hψ z hz)
        ((correspondenceGraphPostcompositionMap f g h ψ hψ z).residueDegree
          (genericPoint (integralComponentAt z).subscheme) : ℤ) :=
  incidenceTorPairing_single_graph_right_eq_single f g h ψ hψ hY z hz

open Classical in
example (hY : (genericPoints Y).Finite) (c : finiteCorrespondences f g) :
    (incidenceTorPairing f g h c (graphCorrespondenceOfComponents g h ψ hψ hY)).val =
      liftFiniteCorrespondence f g (A := AlgebraicCycle (pullback (C := Scheme) f h) ℤ)
        (fun z hz =>
          letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
          finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
            (single (genericPoint (integralComponentAt z).subscheme) 1)) c :=
  congrArg (fun F : finiteCorrespondences f g →+
    AlgebraicCycle (pullback (C := Scheme) f h) ℤ => F c)
    (incidenceTorPairing_graph_right_val_eq_lift f g h ψ hψ hY)

example (hY : (genericPoints Y).Finite) (c : finiteCorrespondences f g) (n : ℤ) :
    incidenceTorPairing f g h (n • c) (graphCorrespondenceOfComponents g h ψ hψ hY) =
      liftFiniteCorrespondence f g (A := finiteCorrespondences f h) (fun z hz =>
        singleFiniteCorrespondence f h
          (correspondenceGraphPostcompositionMap f g h ψ hψ z
            (genericPoint (integralComponentAt z).subscheme))
          (isFiniteCorrespondencePoint_graphPostcomposition_genericPoint f g h ψ hψ z hz)
          ((correspondenceGraphPostcompositionMap f g h ψ hψ z).residueDegree
            (genericPoint (integralComponentAt z).subscheme) : ℤ)) (n • c) :=
  congrArg (fun F : finiteCorrespondences f g →+ finiteCorrespondences f h => F (n • c))
    (incidenceTorPairing_graph_right_eq_lift f g h ψ hψ hY)

open Classical in
example [CompactSpace Y]
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g h ψ hψ
        (finite_genericPoints_of_smooth_of_compact g))).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
      finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
        (single (genericPoint (integralComponentAt z).subscheme) 1) :=
  incidenceTorPairing_single_graph_right_val f g h ψ hψ
    (finite_genericPoints_of_smooth_of_compact g) z hz

example [IsEmpty Y] (hY : (genericPoints Y).Finite) (c : finiteCorrespondences f g) :
    incidenceTorPairing f g h c (graphCorrespondenceOfComponents g h ψ hψ hY) = 0 := by
  rw [graphCorrespondenceOfComponents_eq_zero_of_isEmpty g h ψ hψ hY,
    incidenceTorPairing_zero_right]

end Smooth
