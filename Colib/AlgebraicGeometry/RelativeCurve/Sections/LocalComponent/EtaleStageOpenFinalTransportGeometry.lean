/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenIntegralBaseRefinement
public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartierPullback

/-! # Geometry needed after the actual final descent witness

Properness belongs to every actual component stage, including the existential
final stage selected by root/auxiliary descent. Actual Cartesian section kernels
remain Cartier under each flat map F and kappa. These facts require no supplied
final-frame compatibility and make no new choices of root or stage.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The actual stage structure is proper: its closed component-model inclusion
is followed by the original proper curve's actual base change. -/
instance etaleStageOpenStructure_isProper
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsProper p] [IsClosedImmersion U.ι] (a : Over i) :
    IsProper ((etaleStageOpenStructure X s p i U).app a) := by
  change IsProper (pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι ≫
    pullback.fst ((smallEtaleNeighborhoodOver X s).obj a.left).hom p)
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
