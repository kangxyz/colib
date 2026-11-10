/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Exact
public import Colib.Algebra.Homology.HomologicalComplex.AcyclicKernel

/-!
# The actual ordinary reduced divisor norm is a quasi-isomorphism

The genuine all-degree short exact sequence and the accepted all-degree
acyclicity of its actual boundary-one kernel prove the original unshifted
endpoint. There is no acyclicity premise and no acyclic-cokernel substitution.
This retains arbitrary fields and the original u+1 ordinary coefficients.

Adapted from Motivic/Cohomology/WeightOne/Geometry/WeightOneQuasiIso.lean at
revision a6805c4a87cdfd7717dd7a94039246a167f15380, lines 23-28.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

/-- The genuine ordinary norm is a quasi-isomorphism of the original sheafified chains. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Geometry/WeightOneQuasiIso.lean:23-28"
  "adaptation" "Actual reduced norm quasi-isomorphism using the true acyclic boundary kernel",
  colib_tag "COL-0401"]
instance reducedNormSheafMap_quasiIso : QuasiIso (reducedNormSheafMap k) :=
  HomologicalComplex.quasiIso_of_shortExact_isZero_homology (shortComplex k) (shortExact k)
    (isZero_homology_boundaryOneSheafComplex k)

end AlgebraicGeometry.MotivicCohomology.WeightOne
