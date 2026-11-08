/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFiberBoundaryPath
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
public import Colib.KTheory.Waldhausen.Fibration.IdentityCofiberNormalization

/-!
# Constant-component normalization of the original scalar-cofiber boundary

Left concatenation with the inverse of the original object loop is a genuine homotopy
equivalence. Its value at that object loop has a specified cancellation path to the constant
loop. These two operations, followed by the original loop-degree shift, put both the existing
scalar-cofiber boundary and the independently specified forward scalar square in the actual
coarse K-one group. The boundary class is the inverse of the forward-square class.
The normalization also agrees with the inverse of the original identity-cofiber component
equivalence on the first homotopy group.

No path from the original object loop to the constant loop is assumed. The specified Laurent
automorphism class, its comparison with this forward-square class, and the supported zero-section
boundary formula remain separate interfaces.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberKOneNormalization.lean:80-155`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology HomotopyGroup
open CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

/-- The whole normalized loop retains the inverse prefix and both original cancellation paths.
-/
def perfectOpenObjectLoopNormalizedPath
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    Path (Path.refl (perfectOpenNested j).coarse.kBasepoint)
      (Path.refl (perfectOpenNested j).coarse.kBasepoint) :=
  (loopInversePrefixCancellation ((perfectOpenNested j).coarse.kZeroObjectLoop K)).symm.trans
    (((α.map
      (loopLeftTranslationEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K).symm).continuous
      ).cast (loopLeftTranslationEquiv_apply _ _).symm
        (loopLeftTranslationEquiv_apply _ _).symm).trans
      (loopInversePrefixCancellation ((perfectOpenNested j).coarse.kZeroObjectLoop K)))

/-- The component equivalence sends each actual loop to exactly the displayed normalized loop
class, so its specified translation and both cancellation paths are retained. -/
theorem perfectOpenObjectLoopKOneNormalization_path
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (loopShiftMulEquiv 0 (loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K)
        (FundamentalGroup.fromPath ⟦α⟧))) =
        (FundamentalGroup.fromPath ⟦perfectOpenObjectLoopNormalizedPath j K α⟧) := by
  simp only [loopKOneNormalization, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (pathTransport (loopInversePrefixCancellation ((perfectOpenNested j).coarse.kZeroObjectLoop K))
      1
      (piMap 0
        (loopLeftTranslationEquiv ((perfectOpenNested j).coarse.kZeroObjectLoop K).symm).toFun
        (loopLeftTranslationEquiv_apply _ _)
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦α⟧)))) = _
  rw [piOneEquivFundamentalGroup_pathTransport, HomotopyGroup.mapHom_apply,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality,
    MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  rfl

/-- The explicit inverse prefix agrees with the inverse of the existing identity-cofiber
component equivalence, with the actual loop-degree shift and fundamental-group comparison. -/
theorem perfectOpenObjectLoopKOneNormalization_component
    (a : FundamentalGroup
      (Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K) a =
      (loopShiftMulEquiv 0).symm
        (((perfectOpenNested j).coarse.identityCofiberComponentEquiv K 1).symm
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) := by
  rw [loopKOneNormalization_eq, Structure.identityCofiberComponentEquiv_eq]

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual original scalar-cofiber loop, normalized to the specified coarse K-one group. -/
def perfectScalarCofiberBoundaryKOneClass : (perfectOpenNested j).coarse.K 1 :=
  loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (FundamentalGroup.fromPath ⟦perfectScalarCofiberBoundaryLoop j r q hq K⟧)

/-- The original scalar boundary is the inverse of the independently specified forward square
after the actual inverse-prefix translation, cancellation, and loop-degree shift. -/
theorem perfectScalarCofiberBoundaryKOneClass_eq_inv :
    perfectScalarCofiberBoundaryKOneClass j K r q hq =
      (perfectScalarForwardKOneClass j K r q hq)⁻¹ := by
  have h : ((FundamentalGroup.fromPath ⟦perfectScalarCofiberBoundaryLoop j r q hq K⟧) :
      FundamentalGroup _ ((perfectOpenNested j).coarse.kZeroObjectLoop K)) =
        (FundamentalGroup.fromPath ⟦(perfectScalarWeakLoop j K r q hq).symm⟧) :=
    End.ext (Quotient.sound ⟨perfectScalarCofiberBoundaryOrientation j r q hq K⟩)
  change loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K) _ = _
  rw [h]
  let a : FundamentalGroup
      (Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K) := (FundamentalGroup.fromPath
        ⟦perfectScalarWeakLoop j K r q hq⟧)
  have hi : a⁻¹ =
      (FundamentalGroup.fromPath ⟦(perfectScalarWeakLoop j K r q hq).symm⟧) := rfl
  rw [← hi]
  exact (loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K)).map_inv a

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberKOneNormalization.lean:80-155"
    "adaptation"
  "The actual inverse-prefix cancellation and native generic normalization give the inverse of the
    independently specified forward scalar class"]
  perfectOpenObjectLoopKOneNormalization_path perfectScalarCofiberBoundaryKOneClass_eq_inv

attribute [colib_tag "COL-0304"] perfectScalarCofiberBoundaryKOneClass_eq_inv

end AlgebraicGeometry.Scheme.Modules
