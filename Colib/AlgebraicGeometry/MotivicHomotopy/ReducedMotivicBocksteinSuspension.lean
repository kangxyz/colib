/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.ReducedMotivicBockstein
public import Colib.CategoryTheory.Sites.Simplicial.ReducedCircleCohomology

/-!
# The motivic Bockstein and simplicial suspension

The original finite coefficient Bockstein commutes with the simplicial
circle suspension induced by the reduced cone boundary. The two maps
compose on opposite sides of the same shifted derived Hom class.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Cₖ" => SmoothSite (Spec (CommRingCat.of k))
local notation "Jₖ" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The finite motivic Bockstein commutes with the actual simplicial circle boundary. -/
theorem reducedMotivicModBockstein_circleSuspension
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (q n : ℕ) (p : ℤ)
    (x : (reducedMotivicFiniteCohomology k q n p).obj (op X)) :
    let S := pointedSimplicialCircle.{u + 1} Cₖ
    let K : DerivedCategory (Sheaf Jₖ AddCommGrpCat.{u + 1}) :=
      DerivedCategory.Q.obj (motivicFiniteSheafComplex k q n)
    (reducedMotivicModBockstein k q n (p + 1)).app (op (Under.smash X S))
      (reducedCircleSuspensionHomEquiv Jₖ X K p x) =
      reducedCircleSuspensionHomEquiv Jₖ X K (p + 1)
        ((reducedMotivicModBockstein k q n p).app (op X) x) := by
  intro S K
  let β : ShiftedHom K K (1 : ℤ) :=
    ShiftedHom.map (CochainComplex.finiteCoefficients.modBockstein
      (motivicSheafComplex k q) n) DerivedCategory.Q
  change ShiftedHom ((reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj X) K p at x
  rw [reducedCircleSuspensionHomEquiv_apply, reducedCircleSuspensionHomEquiv_apply]
  let δ := reducedCircleConnecting.{d, u + 1} Jₖ X
  change (δ.comp x rfl).comp β (add_comm 1 (p + 1)) =
    δ.comp (x.comp β (add_comm 1 p)) rfl
  exact ShiftedHom.comp_assoc δ x β rfl (add_comm 1 p)
    (by omega)

attribute [colib_tag "COL-1019"] reducedMotivicModBockstein_circleSuspension

end AlgebraicGeometry.MotivicHomotopy
