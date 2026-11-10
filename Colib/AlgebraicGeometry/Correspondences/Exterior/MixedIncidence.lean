/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport
public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterSquares
public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphComponents

/-!
# Actual mixed graph incidence maps to the literal exterior support

Use the genuine source Cartesian square to lift an actual graph/exterior
incidence back to the original exterior support. The native support isomorphism
preserves the source map, and the graph equation is proved for the actual graph
component. No provider graph equation or cycle multiplicity is assumed.

Adapted from motivic_source_a6805c4, Exterior/Simplex/GraphInterchangeIncidence.lean.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow
variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

/-- The first support point is the actual component point of the parameter graph. -/
abbrev nativeParameterGraphPoint :=
  correspondenceGraphMap (SmoothSite.product X T).hom (SmoothSite.product X U).hom
    (SmoothSite.productMap (𝟙 X) ψ).left (MorphismProperty.Over.w _) t.val

/-- This is the existing native incidence scheme, without a replacement model. -/
abbrev nativeMixedGraphIncidence : Scheme.{u} :=
  correspondenceIncidence (SmoothSite.product X T).hom (SmoothSite.product X U).hom
    (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
    (nativeExteriorPoint X Y U z hz)

/-- Projection of the actual mixed incidence to the source of the parameter graph. -/
abbrev nativeMixedGraphSource : nativeMixedGraphIncidence X Y T U ψ z hz t ⟶
    (SmoothSite.product X T).left :=
  correspondenceIncidenceLeft (SmoothSite.product X T).hom (SmoothSite.product X U).hom
    (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
    (nativeExteriorPoint X Y U z hz)

/-- Projection of the actual mixed incidence to the literal support over the changed parameter. -/
abbrev nativeMixedGraphToChangedSupport : nativeMixedGraphIncidence X Y T U ψ z hz t ⟶
    exteriorIdentitySupport X Y U (integralComponentAt z) :=
  pullback.snd _ _ ≫ (nativeExteriorSupportIso X Y U z hz).inv

/-- Compatibility follows from the actual incidence condition and actual graph equation. -/
theorem nativeMixedGraph_support_condition :
    nativeMixedGraphToChangedSupport X Y T U ψ z hz t ≫
      exteriorIdentitySource X Y U (integralComponentAt z) =
    nativeMixedGraphSource X Y T U ψ z hz t ≫ (SmoothSite.productMap (𝟙 X) ψ).left := by
  dsimp only [nativeMixedGraphToChangedSupport, nativeMixedGraphSource,
    correspondenceIncidenceLeft]
  rw [Category.assoc, nativeExteriorSupportIso_inv_source, ← pullback.condition]
  have hg := nativeGraphComponent_projection_graph (SmoothSite.product X T)
    (SmoothSite.product X U) (SmoothSite.productMap (𝟙 X) ψ) t
  simpa only [nativeGraphComponent, nativeParameterGraphPoint,
    exteriorSupportSourceProjection, exteriorSupportTargetProjection, Category.assoc] using
    congrArg (fun f => pullback.fst _ _ ≫ f) hg.symm

/-- The actual mixed incidence lifts into the literal original exterior support. -/
def nativeMixedGraphToSupport : nativeMixedGraphIncidence X Y T U ψ z hz t ⟶
    exteriorIdentitySupport X Y T (integralComponentAt z) :=
  (exteriorParameterMap_source_isPullback X Y (integralComponentAt z) ψ).lift
    (nativeMixedGraphToChangedSupport X Y T U ψ z hz t)
    (nativeMixedGraphSource X Y T U ψ z hz t)
    (nativeMixedGraph_support_condition X Y T U ψ z hz t)

@[reassoc]
theorem nativeMixedGraphToSupport_parameter :
    nativeMixedGraphToSupport X Y T U ψ z hz t ≫
      exteriorParameterMap X Y (integralComponentAt z) ψ =
    nativeMixedGraphToChangedSupport X Y T U ψ z hz t :=
  IsPullback.lift_fst _ _ _ _

@[reassoc]
theorem nativeMixedGraphToSupport_source :
    nativeMixedGraphToSupport X Y T U ψ z hz t ≫
      exteriorIdentitySource X Y T (integralComponentAt z) =
    nativeMixedGraphSource X Y T U ψ z hz t :=
  IsPullback.lift_snd _ _ _ _

end Stacks.Chow
