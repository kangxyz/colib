/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphLift

/-!
# Native cycle description of the canonical relative graph lift

The coefficient formula and injectivity concern the
actual native cycle, not an arbitrary chosen factorization. This does not yet
state graph-base-change naturality.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable (U Y : SmoothSite (Spec (CommRingCat.of k)))
local notation "B" => SmoothSite.product U Y

/-- The additive prime construction is exactly native closed pushforward. -/
theorem relativeGraphLift_val (a : Cor.mk U ⟶ Cor.mk Y) :
    (relativeGraphLift k U Y a).val = finiteCyclePushforward (ambientLift k U Y) a.val := by
  let L := (finiteCorrespondences U.hom (B).hom).subtype.comp (relativeGraphLift k U Y)
  let R := (finiteCyclePushforward (ambientLift k U Y)).comp
    (finiteCorrespondences U.hom Y.hom).subtype
  have h : L = R := by
    apply finiteCorrespondences.addHom_ext_one U.hom Y.hom
    intro z hz
    change (relativeGraphLift k U Y
      (singleFiniteCorrespondence U.hom Y.hom z hz 1)).val = _
    rw [relativeGraphLift_single, one_smul]
    exact (finiteCyclePushforward_single_of_isClosedImmersion
      (ambientLift k U Y) z 1).symm
  exact DFunLike.congr_fun h a

/-- Closed immersion preserves each signed coefficient, including cancellation. -/
theorem relativeGraphLift_apply_image (a : Cor.mk U ⟶ Cor.mk Y)
    (z : pullback (C := Scheme) U.hom Y.hom) :
    (relativeGraphLift k U Y a).val (ambientLift k U Y z) = a.val z := by
  rw [relativeGraphLift_val]
  exact finiteCyclePushforward_apply_of_isClosedImmersion (ambientLift k U Y) a.val z

/-- No source correspondence information is lost by the actual relative graph lift. -/
theorem relativeGraphLift_injective : Function.Injective (relativeGraphLift k U Y) := by
  intro a b h
  apply Subtype.ext
  apply finiteCyclePushforward_injective_of_isClosedImmersion (ambientLift k U Y)
  simpa only [relativeGraphLift_val] using congrArg Subtype.val h

end AlgebraicGeometry.Cor.RelativeGraph
