/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentAffineSerreLocalization
public import Colib.KTheory.Quillen.Localization.SmallModel

/-!
# Geometric affine coherent localization on the public G-groups

The actual pullback along an affine localization is a Serre localization. Its
kernel yields the canonical supported term and the connecting map, using the
same upper small universe as public scheme G-theory. All three exactness
positions and the surjective degree-zero tail concern these actual maps.

This does not identify the support category with coherent modules annihilated
by an ideal. That identification on G-theory requires the separate dévissage.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/`
`PrincipalLocalization.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`,
with localization at an arbitrary multiplicative set rather than only powers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (S : Submonoid R)

local instance : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) :=
  Modules.Coherent.localizationSpecMap_flat S

/-- The actual supported term of affine coherent localization in the public universe. -/
abbrev affineLocalizationSupportedG (n : ℕ) :=
  SmallModelGLocalization.SupportedK.{u + 1}
    (Modules.Coherent.affineLocalizationExact S) n

/-- Inclusion of the actual coherent localization kernel. -/
def affineLocalizationInclusionG (n : ℕ) : affineLocalizationSupportedG R S n →* G (Spec R) n :=
  SmallModelGLocalization.inclusionKMap.{u + 1}
    (Modules.Coherent.affineLocalizationExact S) n

/-- The canonical boundary from the geometric affine pullback. -/
def affineLocalizationBoundaryG (n : ℕ) :
    G (Spec (CommRingCat.of (Localization S))) (n + 1) →* affineLocalizationSupportedG R S n :=
  SmallModelGLocalization.connectingHom.{u + 1}
    (Modules.Coherent.affineLocalizationExact S) n

/-- Every exactness position and the degree-zero tail for the actual geometric pullback. -/
theorem affineLocalization_longExact :
    (∀ n, (affineLocalizationInclusionG R S n).range =
      (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n).ker) ∧
    (∀ n, (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))
      (n + 1)).range = (affineLocalizationBoundaryG R S n).ker) ∧
    (∀ n, (affineLocalizationBoundaryG R S n).range =
      (affineLocalizationInclusionG R S n).ker) ∧
    Function.Surjective
      (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) 0) :=
  SmallModelGLocalization.localization_longExact.{u + 1}
    (Modules.Coherent.affineLocalizationExact S)

end AlgebraicGeometry.Scheme
