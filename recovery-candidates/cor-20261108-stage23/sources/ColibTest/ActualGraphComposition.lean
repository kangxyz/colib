/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.Composition

/-!
# Actual graph composition regressions

These examples retain arbitrary fields, disconnected or empty smooth schemes,
the exact graph maps, both native support sums, and signed coefficients. They
are source candidates, not executed tests. No associativity input is accepted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

example :
    correspondenceGraphMap f g φ hφ ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) =
      correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) :=
  correspondenceGraphMap_postcomposition f g h φ hφ ψ hψ

example [IsSeparated g] [IsSeparated h] (s : X) (t : Y)
    (hs : Set.range
      ((integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
        pullback.snd f g) ⊆ closure {t}) :
    IsClosedImmersion (correspondenceIncidenceMap f g h
      (correspondenceGraphMap f g φ hφ s) (correspondenceGraphMap g h ψ hψ t)) :=
  isClosedImmersion_correspondenceIncidenceMap_graphMap_comp_of_range_subset
    f g h φ hφ ψ hψ s t hs

end Geometry

section Smooth

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

example (s : genericPoints X) (t : genericPoints Y)
    (hs : Set.range
      ((integralComponentAt (correspondenceGraphMap f g φ hφ s.val)).subschemeι ≫
        pullback.snd f g) ⊆ closure {t.val}) :
    incidenceTorCorrespondence f g h (correspondenceGraphMap f g φ hφ s.val)
      (correspondenceGraphMap g h ψ hψ t.val)
      (isFiniteCorrespondencePoint_graphMap f g φ hφ s)
      (isFiniteCorrespondencePoint_graphMap g h ψ hψ t) =
      singleFiniteCorrespondence f h
        (correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) s.val)
        (isFiniteCorrespondencePoint_graphMap f h (φ ≫ ψ)
          (by rw [Category.assoc, hψ, hφ]) s) 1 :=
  incidenceTorCorrespondence_graphMap_comp_of_range_subset f g h φ hφ ψ hψ s t hs

example (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
    (s t : genericPoints Y) (hst : s ≠ t)
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {s.val}) :
    incidenceTorCorrespondence f g h z (correspondenceGraphMap g h ψ hψ t.val)
      hz (isFiniteCorrespondencePoint_graphMap g h ψ hψ t) = 0 :=
  incidenceTorCorrespondence_graph_right_eq_zero_of_ne f g h z hz ψ hψ s t hst hs

example (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite) :
    incidenceTorPairing f g h
      (graphCorrespondenceOfComponents f g φ hφ hX)
      (graphCorrespondenceOfComponents g h ψ hψ hY) =
      graphCorrespondenceOfComponents f h (φ ≫ ψ)
        (by rw [Category.assoc, hψ, hφ]) hX :=
  incidenceTorPairing_graph_comp f g h φ hφ ψ hψ hX hY

example (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite) (a b : ℤ) :
    incidenceTorPairing f g h
      (a • graphCorrespondenceOfComponents f g φ hφ hX)
      (b • graphCorrespondenceOfComponents g h ψ hψ hY) =
      (a * b) • graphCorrespondenceOfComponents f h (φ ≫ ψ)
        (by rw [Category.assoc, hψ, hφ]) hX :=
  incidenceTorPairing_zsmul_graph_comp f g h φ hφ ψ hψ hX hY a b

example [CompactSpace X] [CompactSpace Y] :
    incidenceTorPairing f g h
      (graphCorrespondenceOfComponents f g φ hφ (finite_genericPoints_of_smooth_of_compact f))
      (graphCorrespondenceOfComponents g h ψ hψ (finite_genericPoints_of_smooth_of_compact g)) =
      graphCorrespondenceOfComponents f h (φ ≫ ψ)
        (by rw [Category.assoc, hψ, hφ]) (finite_genericPoints_of_smooth_of_compact f) :=
  incidenceTorPairing_graph_comp_of_compact f g h φ hφ ψ hψ

-- Smoothness supplies local finite type; quasi-compactness supplies global finite graph support.
example [QuasiCompact f] [QuasiCompact g] :
    ∃ (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite),
      incidenceTorPairing f g h
        (graphCorrespondenceOfComponents f g φ hφ hX)
        (graphCorrespondenceOfComponents g h ψ hψ hY) =
        graphCorrespondenceOfComponents f h (φ ≫ ψ)
          (by rw [Category.assoc, hψ, hφ]) hX := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  exact ⟨finite_genericPoints_of_smooth_of_compact f,
    finite_genericPoints_of_smooth_of_compact g,
    incidenceTorPairing_graph_comp_of_compact f g h φ hφ ψ hψ⟩

example [IsEmpty X] (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite) :
    incidenceTorPairing f g h
      (graphCorrespondenceOfComponents f g φ hφ hX)
      (graphCorrespondenceOfComponents g h ψ hψ hY) = 0 := by
  rw [incidenceTorPairing_graph_comp]
  exact graphCorrespondenceOfComponents_eq_zero_of_isEmpty f h (φ ≫ ψ)
    (by rw [Category.assoc, hψ, hφ]) hX

example [IsEmpty Y] (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite) :
    incidenceTorPairing f g h
      (graphCorrespondenceOfComponents f g φ hφ hX)
      (graphCorrespondenceOfComponents g h ψ hψ hY) = 0 := by
  rw [graphCorrespondenceOfComponents_eq_zero_of_isEmpty g h ψ hψ hY,
    incidenceTorPairing_zero_right]

end Smooth
