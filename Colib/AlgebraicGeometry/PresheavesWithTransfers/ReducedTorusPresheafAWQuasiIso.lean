/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusPresheafAW
public import Colib.AlgebraicTopology.SimplicialObject.AlexanderWhitney

/-!
# The reduced-torus presheaf Alexander–Whitney quasi-isomorphism

Apply the general Alexander–Whitney theorem directly in the abelian monoidal
category of integral presheaves. No evaluation comparison is needed.
This concerns ordinary total tensor; no K-flatness or derived tensor comparison
is asserted.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The original presheaf AW map is a quasi-isomorphism by the general theorem
for abelian monoidal categories with additive tensor. -/
instance reducedTorusPresheafAW_quasiIso (q : ℕ) :
    QuasiIso (reducedTorusPresheafAW k q) :=
  AlgebraicTopology.quasiIso_alexanderWhitney
    (reducedTorusIntSimplicial k q) (reducedTorusIntSimplicial k 1)

end AlgebraicGeometry.PresheafWithTransfers
