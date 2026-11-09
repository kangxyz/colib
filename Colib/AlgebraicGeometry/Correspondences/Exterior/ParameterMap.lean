/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support

/-!
# Actual support maps induced by parameter morphisms

A morphism of smooth parameters acts on the literal exterior support by native
pullback.map. Both original support projections commute with the corresponding
product maps. These are support-level identities; no pushforward multiplicity or
composition of correspondence cycles is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow
variable {S : Scheme.{u}} (X Y : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)
  {T U V : SmoothSite S}

/-- The literal map of actual exterior supports induced by a parameter map. -/
def exteriorParameterMap (ψ : T ⟶ U) :
    exteriorIdentitySupport X Y T W ⟶ exteriorIdentitySupport X Y U W :=
  pullback.map _ _ _ _ (𝟙 W.subscheme) ψ.left (𝟙 S) (by simp)
    (by simp)

@[reassoc (attr := simp)]
theorem exteriorParameterMap_fst (ψ : T ⟶ U) :
    exteriorParameterMap X Y W ψ ≫
      pullback.fst (exteriorSupport_sourceProjection X Y W ≫ X.hom) U.hom =
    pullback.fst (exteriorSupport_sourceProjection X Y W ≫ X.hom) T.hom := by
  simp [exteriorParameterMap]

@[reassoc (attr := simp)]
theorem exteriorParameterMap_snd (ψ : T ⟶ U) :
    exteriorParameterMap X Y W ψ ≫
      pullback.snd (exteriorSupport_sourceProjection X Y W ≫ X.hom) U.hom =
    pullback.snd (exteriorSupport_sourceProjection X Y W ≫ X.hom) T.hom ≫ ψ.left := by
  simp [exteriorParameterMap]

@[simp]
theorem exteriorParameterMap_id : exteriorParameterMap X Y W (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

@[simp]
theorem exteriorParameterMap_comp (ψ : T ⟶ U) (χ : U ⟶ V) :
    exteriorParameterMap X Y W (ψ ≫ χ) =
      exteriorParameterMap X Y W ψ ≫ exteriorParameterMap X Y W χ := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Source-product naturality for the actual support map. -/
@[reassoc]
theorem exteriorParameterMap_source (ψ : T ⟶ U) :
    exteriorParameterMap X Y W ψ ≫ exteriorIdentitySource X Y U W =
    exteriorIdentitySource X Y T W ≫ (SmoothSite.productMap (𝟙 X) ψ).left := by
  apply pullback.hom_ext <;> simp [Category.assoc, SmoothSite.productMap, SmoothSite.productLift,
    SmoothSite.productFst, SmoothSite.productSnd]

/-- Target-product naturality uses the very same parameter map. -/
@[reassoc]
theorem exteriorParameterMap_target (ψ : T ⟶ U) :
    exteriorParameterMap X Y W ψ ≫ exteriorIdentityTarget X Y U W =
    exteriorIdentityTarget X Y T W ≫ (SmoothSite.productMap (𝟙 Y) ψ).left := by
  apply pullback.hom_ext <;> simp [Category.assoc, SmoothSite.productMap, SmoothSite.productLift,
    SmoothSite.productFst, SmoothSite.productSnd]

end Stacks.Chow
