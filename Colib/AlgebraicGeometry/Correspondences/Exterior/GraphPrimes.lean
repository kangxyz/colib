/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphComponents
public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphComparison
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Generics
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Prime
public import Colib.AlgebraicGeometry.Correspondences.Additive

/-!
# Actual exterior images of native graph-component primes

The actual image ideal of a native graph component times the parameter identity
is the native component of the actual product graph at the corresponding actual
generic point. The resulting native prime cycles are equal, with coefficient
one. No component comparison or graph equation is supplied as a provider.
Adapted from motivic_source_a6805c4, Exterior/Simplex/Graph.lean.
The finite sum of components is handled separately.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] (φ : X ⟶ Y) (t : genericPoints X.left)

/-- Equality of the actual native image ideals of the two graph-component constructions. -/
theorem nativeExteriorImage_eq_productGraphComponent :
    (exteriorIdentityInclusion X Y T (nativeGraphComponent X Y φ t)).ker =
      nativeGraphComponent (SmoothSite.product X T) (SmoothSite.product Y T)
        (SmoothSite.productMap φ (𝟙 T)) (exteriorSourceGenericsEquiv X T t) := by
  let hz := isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left
    (MorphismProperty.Over.w φ) t
  let : IsFinite (exteriorSupportSourceProjection X Y (nativeGraphComponent X Y φ t)) := hz.1
  refine nativeIntegralGraphSupport_eq_of_sourceRange_eq
    (SmoothSite.product X T) (SmoothSite.product Y T) _ _
    (nativeExteriorImage_isIntegral X Y T _ hz)
    (isIntegral_integralComponentAt _) (SmoothSite.productMap φ (𝟙 T)) ?_ ?_ ?_
  · simpa only [exteriorSupportSourceProjection, exteriorSupportTargetProjection,
      Category.assoc] using exteriorIdentityImage_graph X Y T (nativeGraphComponent X Y φ t)
        φ (nativeGraphComponent_projection_graph X Y φ t)
  · exact nativeGraphComponent_projection_graph (SmoothSite.product X T)
      (SmoothSite.product Y T) (SmoothSite.productMap φ (𝟙 T))
      (exteriorSourceGenericsEquiv X T t)
  · change Set.range
      ((exteriorIdentityInclusion X Y T (nativeGraphComponent X Y φ t)).ker.subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) = _
    rw [exteriorIdentityImage_range, nativeGraphComponent_source_range X Y φ t,
      nativeGraphComponent_source_range (SmoothSite.product X T) (SmoothSite.product Y T)
        (SmoothSite.productMap φ (𝟙 T)) (exteriorSourceGenericsEquiv X T t)]
    exact (exteriorSourceGenericsEquiv_closure X T t).symm

/-- Actual exterior extension sends an original graph prime to the product graph prime. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:120-147"
  "adaptation" "Equality of actual native exterior graph-component primes"]
theorem nativeExteriorPrime_graph :
    nativeExteriorPrime X Y T
      (correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) t.val)
      (isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) t) =
    singleFiniteCorrespondence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (correspondenceGraphMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.productMap φ (𝟙 T)).left (MorphismProperty.Over.w _)
        (exteriorSourceGenericsEquiv X T t).val)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w _) (exteriorSourceGenericsEquiv X T t)) 1 := by
  classical
  have hp : genericPointOf
      (exteriorIdentityInclusion X Y T (nativeGraphComponent X Y φ t)).ker
      (nativeExteriorImage_isIntegral X Y T _
        (isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left
          (MorphismProperty.Over.w φ) t)) =
      correspondenceGraphMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.productMap φ (𝟙 T)).left (MorphismProperty.Over.w _)
        (exteriorSourceGenericsEquiv X T t).val := by
    simp only [nativeExteriorImage_eq_productGraphComponent, nativeGraphComponent,
      genericPointOf_integralComponentAt]
  apply Subtype.ext
  change single _ (1 : ℤ) = single _ (1 : ℤ)
  exact congrArg (fun z => single z (1 : ℤ)) hp

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:120-147"
  "adaptation"
    "Literal native exterior image ideal equals the corresponding product graph component"]
  nativeExteriorImage_eq_productGraphComponent

end Stacks.Chow
