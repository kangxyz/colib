/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.RestrictionInvariance
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
import Colib.AlgebraicGeometry.MotivicCohomology.AffineLineInvariance
import Colib.Util.References

/-!
# A¹-invariance with finite motivic coefficients

The actual affine-line projection is invertible for the integral coefficient
complex in every degree, hence for the literal multiplication cone.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual motivic cohomology presheaf with cone coefficients is invariant
under the affine-line projection over a perfect field. -/
@[colib_tag "COL-1033"]
theorem motivicFiniteCohomologyPresheaf_isA1Invariant (p : ℤ) (q n : ℕ) :
    A1.IsInvariant (.of k) (motivicFiniteCohomologyPresheaf k p q n) := by
  intro X
  exact isIso_motivicFiniteCohomologyRestriction_of_integral k
    ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X) q n
    (fun i ↦ motivicCohomologyPresheaf_isA1Invariant k i q X) p

end AlgebraicGeometry.PresheafWithTransfers
