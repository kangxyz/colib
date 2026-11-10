/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedGraphPushforward
public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-!
# Actual graph interchange for signed native exterior correspondences

For an arbitrary parameter morphism T → U, left composition of the actual
X-parameter graph with the U-exterior of a signed correspondence equals right
composition of its T-exterior with the actual Y-parameter graph.

For each admissible prime, actual component selection leaves exactly one graph
summand. Its coefficient is computed from actual stalk Tor, and its finite map
is identified with the actual right-graph support map. All other incidences are
empty. Additive extensionality on the native finite-correspondence subgroup then
retains every original integer coefficient, including negative coefficients.

This is a new native assembly of the authenticated mixed-incidence geometry and
right-graph pushforward, not a claim of verbatim recovery of an uninspected legacy
assembly file. It requires geometrically integral T and U, as do both native
exterior operations. It does not require the parameter morphism to be flat.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "gT" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "ΓX" =>
  graphCorrespondenceOfComponents f g (SmoothSite.productMap (𝟙 X) ψ).left
    (MorphismProperty.Over.w _) (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product X T)))
local notation3 (prettyPrint := false) "ΓY" =>
  graphCorrespondenceOfComponents gT h (SmoothSite.productMap (𝟙 Y) ψ).left
    (MorphismProperty.Over.w _) (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product Y T)))

/-- The complete left parameter graph sum has exactly one nonzero actual incidence term. -/
theorem nativeExteriorPrime_graph_left_eq_matching
    (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    incidenceTorPairing f g h ΓX (nativeExteriorPrime X Y U z hz) =
      incidenceTorCorrespondence f g h
        (nativeParameterGraphPoint X T U ψ (nativeMixedMatchingComponent X Y T z hz))
        (nativeExteriorPoint X Y U z hz)
        (isFiniteCorrespondencePoint_graphMap f g (SmoothSite.productMap (𝟙 X) ψ).left
          (MorphismProperty.Over.w _) (nativeMixedMatchingComponent X Y T z hz))
        (nativeExteriorPoint_admissible X Y U z hz) := by
  classical
  let := (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product X T))).fintype
  change (incidenceTorPairing f g h).flip (nativeExteriorPrime X Y U z hz) ΓX = _
  rw [nativeExteriorPrime_eq_single,
    graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  simp only [AddMonoidHom.flip_apply, incidenceTorPairing_single_one]
  apply Finset.sum_eq_single (nativeMixedMatchingComponent X Y T z hz)
  · intro t ht hne
    exact nativeMixedGraphIncidenceTor_eq_zero_of_ne_matching X Y T z hz U ψ t hne
  · simp

/-- Prime graph interchange follows from the actual Tor cycle and equality of the finite maps. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/\
    GraphInterchangeIncidence.lean:292-334"
  "adaptation" "New native assembly using empty nonmatching incidence and the actual \
    matching finite map",
  colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeRight.lean:72-97"
  "adaptation" "Comparison with the actual degree-weighted right-graph pushforward"]
theorem nativeExteriorPrime_graph_interchange
    (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    incidenceTorPairing f g h ΓX (nativeExteriorPrime X Y U z hz) =
      incidenceTorPairing f gT h (nativeExteriorPrime X Y T z hz) ΓY := by
  rw [nativeExteriorPrime_graph_left_eq_matching]
  apply Subtype.ext
  exact (nativeMixedMatchingIncidenceTor_val X Y T U ψ z hz).trans
    (nativeExteriorPrime_graph_right_val X Y T z hz (SmoothSite.product Y U)
      (SmoothSite.productMap (𝟙 Y) ψ)).symm

/-- Actual graph interchange on every signed native finite correspondence.
Both graph sums, both exterior operations, and both compositions are the existing native ones. -/
@[colib_tag "COL-0389",
  colib_ref "MVW2006" "Lecture 1, Definition 1.9, printed p. 6"
  "adaptation" "Exterior-product conventions only; this definition does not state graph \
    interchange, which is proved here from the actual Tor and finite-support-map comparisons",
  stacks 02R4 "application: actual finite support maps are proper and retain their \
    residue degrees; no properness of the parameter morphism is assumed",
  stacks 02R5 "application: functoriality for the actual finite support maps through the \
    incidence isomorphism"]
theorem nativeExterior_graph_interchange (α : finiteCorrespondences X.hom Y.hom) :
    incidenceTorPairing f g h ΓX (nativeExterior X Y U α) =
      incidenceTorPairing f gT h (nativeExterior X Y T α) ΓY := by
  let F := (incidenceTorPairing f g h ΓX).comp (nativeExterior X Y U)
  let G := ((incidenceTorPairing f gT h).flip ΓY).comp (nativeExterior X Y T)
  have hFG : F = G := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    change incidenceTorPairing f g h ΓX
        (nativeExterior X Y U (singleFiniteCorrespondence X.hom Y.hom z hz 1)) =
      incidenceTorPairing f gT h
        (nativeExterior X Y T (singleFiniteCorrespondence X.hom Y.hom z hz 1)) ΓY
    simp only [nativeExterior_single, one_smul]
    exact nativeExteriorPrime_graph_interchange X Y T U ψ z hz
  exact congrArg (fun L : finiteCorrespondences X.hom Y.hom →+
    finiteCorrespondences f h => L α) hFG

end Stacks.Chow
