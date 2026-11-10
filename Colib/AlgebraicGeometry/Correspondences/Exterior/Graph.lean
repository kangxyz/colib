/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphPrimes
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Additive
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Native exterior operation on actual graph cycles and identities

Reindex the genuine finite sum of graph components by the native generic-point
bijection. Each actual exterior prime is its corresponding product graph prime,
with coefficient one. This retains empty and disconnected sources and arbitrary
fields. The identity law follows from the actual graph functor and product map.
Composition on arbitrary signed correspondences remains a separate obligation.
Adapted from motivic_source_a6805c4, Exterior/Simplex/Graph.lean and Identity/Unit.lean.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

/-- The signed native exterior operation preserves the actual full graph cycle. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:176-222"
  "adaptation" "Native exterior of the actual graph equals the actual product graph"]
theorem nativeExterior_graphFunctor (φ : X ⟶ Y) :
    nativeExterior X Y T ((Cor.graphFunctor k).map φ) =
      (Cor.graphFunctor k).map (SmoothSite.productMap φ (𝟙 T)) := by
  classical
  let := (Cor.finite_genericPoints k (Cor.mk X)).fintype
  let := (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product X T))).fintype
  change nativeExterior X Y T
      (graphCorrespondenceOfComponents X.hom Y.hom φ.left
        (MorphismProperty.Over.w φ) (Cor.finite_genericPoints k (Cor.mk X))) =
    graphCorrespondenceOfComponents (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (SmoothSite.productMap φ (𝟙 T)).left (MorphismProperty.Over.w _)
      (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product X T)))
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence,
    graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  simp_rw [nativeExterior_single, one_zsmul, nativeExteriorPrime_graph]
  exact (exteriorSourceGenericsEquiv X T).sum_comp (fun s =>
    singleFiniteCorrespondence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (correspondenceGraphMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.productMap φ (𝟙 T)).left (MorphismProperty.Over.w _) s.val)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w _) s) 1)

/-- Identities are preserved on the actual native correspondence object. -/
@[simp↓]
theorem nativeExterior_id :
    nativeExterior X X T (𝟙 (Cor.mk X)) = 𝟙 (Cor.mk (SmoothSite.product X T)) := by
  have h := nativeExterior_graphFunctor X X T (𝟙 X)
  rw [SmoothSite.productMap_id] at h
  exact (congrArg (nativeExterior X X T) ((Cor.graphFunctor k).map_id X)).symm.trans
    (h.trans ((Cor.graphFunctor k).map_id (SmoothSite.product X T)))

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Unit.lean:151-193"
  "adaptation"
    "Native identity equality for every smooth source and geometrically integral parameter"]
  nativeExterior_id

attribute [colib_tag "COL-0388"]
  nativeExterior_graphFunctor
  nativeExterior_id

end Stacks.Chow
