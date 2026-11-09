/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedQcqsRoof
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedQcqsStabilization

/-!
# Supported qcqs geometry: roofs and stabilized extensions

The supported source of the roof is constructed with the original global endpoints.
The supported complement is the actual shift of the local complex. These are geometric
inputs for later supported fine localization; they do not assert the saturated-image
factorization, cofinality, positive comparison, degree-zero comparison, or Bass theorem.
-/

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/\
      OpenDerivedImage/SupportedRoofs.lean:36-125"
    "adaptation"
    "Actual supported qcqs roofs from union extension by zero, with fixed global endpoints; \
      compact union is assumed and the numerator target may have only QC homology"]
  exists_perfectSupported_chainMap_roof_of_union_compact
  exists_perfectSupported_chainMap_roof_of_qcqs

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/\
      GlobalSupportedDensity.lean:143-199"
    "adaptation"
    "Supported complementary extension, strengthened to the actual shift complement via \
      union extension by zero; not the old finite-affine induction proof"]
  exists_perfectSupported_restrict_iso_biprod_shift_of_union_compact
  exists_perfectSupported_restrict_iso_biprod_shift_of_qcqs
  exists_perfectSupported_restrict_stabilization_of_union_compact
  exists_perfectSupported_restrict_stabilization_of_qcqs

attribute [colib_tag "COL-0333"]
  exists_perfectSupported_chainMap_roof_of_union_compact
  exists_perfectSupported_restrict_iso_biprod_shift_of_union_compact

end AlgebraicGeometry.Scheme.Modules
