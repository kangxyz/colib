/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Point
public import Colib.Topology.Homotopy.Extension

/-! # The genuine chosen-point HEP of the singleton prespectrum

The existing literal point prespectrum has HEP because its chosen-point inclusion is
the identity. No replacement point object is introduced.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace Topology.LoopPrespectrum

/-- The literal chosen point of the singleton prespectrum has HEP in every level. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/Point.lean:34"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem pointPrespectrum_point_homotopyExtensionProperty (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} (pointPrespectrum.{u}.point n))) := by
  have he : TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (pointPrespectrum.{u}.point n)) =
      𝟙 (TopCat.of PUnit.{u + 1}) := by
    ext x
    change (PUnit.unit : PUnit.{u + 1}) = x
    exact Subsingleton.elim _ _
  rw [he]
  exact TopCat.homotopyExtensionProperty_of_isIso _

end Topology.LoopPrespectrum
