/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RowRefinementHomotopy
public import Colib.Topology.Prespectrum.RowRefinementFunctoriality
public import Colib.Topology.Prespectrum.RowInterchangeMappingCone

/-!
# Actual row strength for the original quotient cone

The original target inclusion and the full prescribed cone null descend to a whole map from
the cone of a row-refined map to the row refinement of its original cone. The cone height
and all row coordinates remain independent, including the double row at degree zero.
This constructs only a forward map; no stable equivalence or inverse is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (hf : ∀ k x, qF k (f.map (k + 3) x) = f.map (k + 3) (qE k x))

/-- The original target inclusion acts pointwise on the actual row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementCone.lean:34-38"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def coneInclusion : spectrum F qF hF ⟶ spectrum (mappingCone f)
    (RowInterchange.cone f qE qF hE hF hf) (RowInterchange.cone_point f qE qF hE hF hf) :=
  map qF _ hF _ (mappingConeInclusion f) (fun _ _ => rfl)

/-- The entire prescribed cone null acts pointwise without altering its cone height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementCone.lean:39-48"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def coneNull : Homotopy (map qE qF hE hF f hf ≫ coneInclusion f qE qF hE hF hf)
    (zeroHom (spectrum E qE hE) (spectrum (mappingCone f)
      (RowInterchange.cone f qE qF hE hF hf) (RowInterchange.cone_point f qE qF hE hF hf))) :=
  (homotopy qE _ hE _
    (fun k x => congrArg ((mappingConeInclusion f).map (k + 3)) (hf k x))
    (fun k _ => RowInterchange.cone_point f qE qF hE hF hf k)
    (mappingConeHomotopy f) (fun _ _ _ => rfl)).cast
      (map_comp _ _ _ _ _ _ _ _ _ _ _) (map_zero _ _ _ _ _)

/-- The same original cone quotient descends to its genuine forward row comparison. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementCone.lean:49-53"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def coneStrength : mappingCone (map qE qF hE hF f hf) ⟶ spectrum (mappingCone f)
    (RowInterchange.cone f qE qF hE hF hf) (RowInterchange.cone_point f qE qF hE hF hf) :=
  mappingConeDesc _ (coneInclusion f qE qF hE hF hf) (coneNull f qE qF hE hF hf)

/-- The original target inclusion commutes strictly with the complete row strength. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementCone.lean:54-58"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem coneStrength_inclusion :
    mappingConeInclusion (map qE qF hE hF f hf) ≫ coneStrength f qE qF hE hF hf =
      coneInclusion f qE qF hE hF hf := mappingConeInclusion_desc ..

/-- Positive levels retain the entire prescribed null at the original cone height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementCone.lean:59-65"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem coneStrength_cylinder_succ (k : ℕ) (t s : unitInterval)
    (γ : Path (E.point (k + 2)) (E.point (k + 2))) :
    Path.toContinuousMap ((coneStrength f qE qF hE hF hf).map (k + 1)
      ((mappingConeHomotopy (map qE qF hE hF f hf)).level (k + 1) (t, γ))) s =
      (mappingConeHomotopy f).level (k + 2) (t, γ s) := rfl

/-- The zero level preserves both row parameters and the independent cone height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementCone.lean:66-71"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem coneStrength_cylinder_zero (t r s : unitInterval)
    (γ : Path (Path.refl (E.point 2)) (Path.refl (E.point 2))) :
    Path.toContinuousMap (Path.toContinuousMap ((coneStrength f qE qF hE hF hf).map 0
      ((mappingConeHomotopy (map qE qF hE hF f hf)).level 0 (t, γ))) r) s =
      (mappingConeHomotopy f).level 2 (t, γ r s) := rfl

end Topology.LoopPrespectrum.RowRefinement
