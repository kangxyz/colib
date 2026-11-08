/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFinitePullbackStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorModule
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteOriginalList

/-!
# The actual right finite Tor stalk is the original G,H tensor-Tor coefficient

Restrict the actual finite-model stalk along its actual projection isomorphism and the
proved equality of original exterior points. Native pullback-stalk comparison and the
existing actual right exterior Tor-sheaf comparison identify it with precisely
P tensor over P0 original Tor(G,H), in the same degree and linearly over the full P.
The scalar map is the literal transported projection map, not an input action.
No Z presentation, flat finite map or coefficient comparison is required.
References: Stacks 0098 and 0AZT. Ordered original Y compatibility is supplied separately
by RightRemainingFiniteOriginalList and used in the Euler leaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual original right-stage action on the same finite Tor-sheaf stalk. -/
@[instance_reducible]
def correspondenceRightRemainingFiniteTorStalkStageModule
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) (n : ℕ) :
    Module ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y))
        ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) := by
  let := stalkModule (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n) q
  exact Module.compHom _
    ((((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
      (Inseparable.of_eq hρ)).hom ≫
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x).stalkMap q).hom)

/-- Original G,H Tor, with its actual quotient action, computes every finite-model stalk. -/
def correspondenceRightRemainingFiniteOriginalPairStalkLinearEquiv [IsSeparated h]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) (n : ℕ) :
    let a := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk a
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π a)
    letI := correspondenceIncidenceTorModule g h i w v (π a) n
    letI : Algebra P₀ P := (π.stalkMap a).hom.toAlgebra
    letI := correspondenceRightRemainingFiniteTorStalkStageModule f g h i z w v x q y hρ n
    ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a) n) := by
  dsimp only
  let F := correspondenceRightIntermediateSupportProduct f g h i z w v
  let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  let M := correspondenceRightExteriorTorSheaf f g h i z w v n
  let ePBAt (a : F) (ha : a = ρ q) :
      let P := F.presheaf.stalk a
      let M' := (Scheme.Modules.pullback ρ).obj M
      letI := stalkModule M' q
      letI := stalkModule M a
      letI : Module P (M'.presheaf.stalk q) := Module.compHom _
        (((F.presheaf.stalkCongr (Inseparable.of_eq ha)).hom ≫ ρ.stalkMap q).hom)
      (M'.presheaf.stalk q) ≃ₗ[P] (M.presheaf.stalk a) := by
    subst a
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] using
        correspondenceRightRemainingFinitePullbackStalkLinearEquiv f g h i z w v x q M
  exact (ePBAt (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y) hρ).trans
    (correspondenceRightExteriorTorSheafStalkIso f g h i z w v
      (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y) n).toLinearEquiv

end Stacks.Chow
