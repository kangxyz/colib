/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiberComponents
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatLeftCoefficient

/-!
# Flat graph precomposition of a full integral support fiber

Actual positive Tor vanishing for a flat left graph and the native disjoint
clopen graph-component cover identify composition with the entire support
fiber. No flatness of the individual support over the original source is used.
The source may be empty or disconnected.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

open Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.SmoothSite (Spec (.of k))}
  (φ : X ⟶ Y) [Flat φ.left]
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

/-- The actual flat graph composed with a prime support is the whole Cartesian fiber,
for arbitrary smooth sources including disconnected and empty ones. -/
theorem graph_comp_single_val_eq_fiber_of_flat :
    letI := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left
      (MorphismProperty.Over.w φ) hw
    letI := isNoetherian_correspondenceGraphFiber (X := X.left) Y.hom Z.hom w φ.left hw
    ((graphFunctor k).map φ ≫ singleFiniteCorrespondence Y.hom Z.hom w hw 1).val =
      finiteCyclePushforward
        (correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left (MorphismProperty.Over.w φ))
        (AlgebraicCycle.fundamentalCycle (correspondenceGraphFiber Y.hom Z.hom w φ.left)) := by
  classical
  haveI := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left
    (MorphismProperty.Over.w φ) hw
  haveI := isNoetherian_correspondenceGraphFiber (X := X.left) Y.hom Z.hom w φ.left hw
  letI := (finite_genericPoints k (Cor.mk X)).fintype
  let z (s : genericPoints X.left) :=
    correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) s.val
  let hz (s : genericPoints X.left) :=
    isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) s
  haveI : ∀ s : genericPoints X.left,
      IsNoetherian (correspondenceIncidence X.hom Y.hom Z.hom (z s) w) :=
    fun s => isNoetherian_correspondenceIncidence_of_finite_source
      X.hom Y.hom Z.hom (z s) w (hz s) hw
  haveI : ∀ s : genericPoints X.left,
      IsFinite (correspondenceIncidenceMap X.hom Y.hom Z.hom (z s) w) :=
    fun s => isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom (z s) w (hz s) hw
  rw [graph_comp_single_eq_sum_incidence]
  simp only [one_smul]
  change (finiteCorrespondences X.hom Z.hom).subtype
      (∑ s : genericPoints X.left,
        incidenceTorCorrespondence X.hom Y.hom Z.hom (z s) w (hz s) hw) = _
  rw [map_sum, fundamentalCycle_graphFiber_eq_sum_incidence
    X.hom Y.hom Z.hom φ.left (MorphismProperty.Over.w φ) w, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [incidenceTorCorrespondence_val,
    incidenceTorCycle_eq_fundamentalCycle_of_flat_graph
      X.hom Y.hom Z.hom φ.left (MorphismProperty.Over.w φ) s w hw,
    finiteCyclePushforward_comp_apply, correspondenceLeftGraphFiberMap_outer]

end AlgebraicGeometry.Cor
