/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Additive
public import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition
public import Colib.AlgebraicGeometry.Correspondences.Category

/-!
# Actual right-graph Tor composition of native exterior primes

The actual exterior prime is the native single cycle at its image generic point.
Its composition with an arbitrary actual target graph is the existing finite
pushforward of that support prime, with its actual residue degree retained.
This reuses the native right-graph Tor theorem; it does not assume a cycle-level
parameter interchange or replace any residue degree by one.

Source: motivic_source_a6805c4, Exterior/Simplex/GraphInterchangeRight.lean.
Native finite pushforward conventions: Stacks 02R4 and 02R5.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
universe u
namespace Stacks.Chow
attribute [local instance] isIntegral_integralComponentAt
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

/-- The point is the genuine image-ideal generic point of the exterior support. -/
abbrev nativeExteriorPoint :=
  genericPointOf (exteriorIdentityInclusion X Y T (integralComponentAt z)).ker
    (nativeExteriorImage_isIntegral X Y T z hz)

/-- Admissibility follows from the existing actual cycle with coefficient one. -/
theorem nativeExteriorPoint_admissible :
    IsFiniteCorrespondencePoint (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (nativeExteriorPoint X Y T z hz) := by
  apply (nativeExteriorPrime X Y T z hz).property.2
  rw [nativeExteriorPrime_apply]
  exact one_ne_zero

/-- No auxiliary generator model is introduced when exposing the native prime. -/
theorem nativeExteriorPrime_eq_single :
    nativeExteriorPrime X Y T z hz =
      singleFiniteCorrespondence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint_admissible X Y T z hz) 1 := by
  apply Subtype.ext
  rfl

open Classical in
/-- Right composition is the actual degree-weighted native finite pushforward. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeRight.lean:72-97"
  "adaptation" "Actual native exterior prime right-graph finite pushforward",
  stacks 02R4 "Native finite pushforward retains actual residue degrees"]
theorem nativeExteriorPrime_graph_right_val
    (Z : SmoothSite (Spec (.of k))) (ψ : SmoothSite.product Y T ⟶ Z) :
    (incidenceTorPairing (SmoothSite.product X T).hom (SmoothSite.product Y T).hom Z.hom
      (nativeExteriorPrime X Y T z hz)
      (graphCorrespondenceOfComponents (SmoothSite.product Y T).hom Z.hom ψ.left
        (MorphismProperty.Over.w ψ)
        (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product Y T))))).val =
      letI := isFinite_correspondenceGraphPostcompositionMap
        (SmoothSite.product X T).hom (SmoothSite.product Y T).hom Z.hom ψ.left
        (MorphismProperty.Over.w ψ) (nativeExteriorPoint X Y T z hz)
        (nativeExteriorPoint_admissible X Y T z hz)
      finiteCyclePushforward
        (correspondenceGraphPostcompositionMap (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom Z.hom ψ.left (MorphismProperty.Over.w ψ)
          (nativeExteriorPoint X Y T z hz))
        (single (genericPoint (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme)
          1) := by
  rw [nativeExteriorPrime_eq_single]
  exact incidenceTorPairing_single_graph_right_val (SmoothSite.product X T).hom
    (SmoothSite.product Y T).hom Z.hom ψ.left (MorphismProperty.Over.w ψ)
    (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product Y T)))
    (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint_admissible X Y T z hz)

end Stacks.Chow
