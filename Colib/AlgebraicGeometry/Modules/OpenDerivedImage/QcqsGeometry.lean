/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectQcqsComplement
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Roofs
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Complements

/-!
# Qcqs geometry for the honest derived image of perfect restriction

For a quasi-compact open immersion into a quasi-compact quasi-separated scheme, the actual
native perfect roof and complement theorems discharge the geometric inputs of the honest
restriction image. Neither input is assumed. These results concern geometry, not a complete
connective image-cover localization or a nonconnective Bass fiber sequence.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] [HasDerivedCategory.{d} U.Modules]

/-- Restricted derived morphisms between global native perfect models admit actual perfect
chain-map roofs on a qcqs scheme. The chosen derived model on the open is arbitrary. -/
@[colib_tag "COL-0307"]
theorem hasDerivedRoofs_of_qcqs : HasDerivedRoofs j :=
  fun A P hA hP α => exists_isPerfectComplex_chainMap_roof_of_perfect j A P hA hP α

/-- Every native perfect complex on the quasi-compact open has an actual perfect complement
whose sum is the derived restriction of a global native perfect complex. -/
@[colib_tag "COL-0307"]
theorem hasPerfectComplements_of_qcqs : HasPerfectComplements j :=
  fun P hP => exists_isPerfectComplex_restrict_complement j P hP

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
