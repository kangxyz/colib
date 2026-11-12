/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PrincipalClosedLocalization

/-!
# The original geometric principal boundary under affine global sections

The actual public coherent boundary agrees with the original finite-module
boundary. The proof uses the closed direct-image square in the supported
categories and the original boundary universe naturality, not cancellation
of ambient G-group inclusions or an unspecified isomorphism of groups.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/`
`PrincipalBoundaryComparison.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

set_option maxHeartbeats 1000000 in
-- Keep the actual geometric boundary and the supported global-sections square explicit.
private theorem closedBoundary_into_upperKernel (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of (Localization.Away f))) (n + 1)) :
    (upperSupportedGlobalSectionsExact (Submonoid.powers f)).KMap n
      (PrincipalClosed.closedSupportGEquiv R f n (Scheme.PrincipalClosed.boundaryG R f n a)) =
    SmallModelGLocalization.connectingHom.{u + 1}
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f)) n
        ((affineGlobalSectionsExact (CommRingCat.of (Localization.Away f))).smallKMap.{u + 1}
          (n + 1) a) := by
  have hc : PrincipalClosed.closedSupportGEquiv R f n
      (Scheme.PrincipalClosed.boundaryG R f n a) =
      SmallModelGLocalization.connectingHom.{u + 1}
        (affineLocalizationExact (Submonoid.powers f)) n a :=
    (PrincipalClosed.closedSupportGEquiv R f n).apply_symm_apply _
  apply (congrArg ((upperSupportedGlobalSectionsExact (Submonoid.powers f)).KMap n) hc).trans
  exact DFunLike.congr_fun
    (SmallModelBoundaryNaturality.Square.connecting_naturality.{u + 1}
      (affineLocalizationExact (Submonoid.powers f))
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f))
      (affineGlobalSectionsExact R)
      (affineGlobalSectionsExact (CommRingCat.of (Localization.Away f)))
      (coherentLocalizationGlobalSectionsIso (Submonoid.powers f)) n) a

set_option maxHeartbeats 1000000 in
-- The original supported routes retain the geometric functors and both small universes.
/-- The actual public principal boundary is the original finite-module boundary under Γ. -/
theorem publicSpecGRingEquiv_principalClosed_boundaryG (n : ℕ) :
    (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n).toMonoidHom.comp
      (Scheme.PrincipalClosed.boundaryG R f n) =
    (FGModuleCat.Localization.closedConnectingHom.{u, u} f n).comp
      (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1)).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  apply (FGModuleCat.Localization.closedSupportGEquiv.{u, u} f n).injective
  apply (ExactFunctor.universalKEquivOfMapQIsEquivalence
    (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f))) n).injective
  change (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f))).universalKMap n
        (FGModuleCat.Localization.closedSupportGEquiv.{u, u} f n
          (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n
            (Scheme.PrincipalClosed.boundaryG R f n a))) =
    (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f))).universalKMap n
        (FGModuleCat.Localization.closedSupportGEquiv.{u, u} f n
          (FGModuleCat.Localization.closedConnectingHom.{u, u} f n
            (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a)))
  have hc : FGModuleCat.Localization.closedSupportGEquiv.{u, u} f n
      (FGModuleCat.Localization.closedConnectingHom.{u, u} f n
        (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a)) =
    FGModuleCat.Localization.connectingHom (Submonoid.powers f) n
      (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a) :=
    (FGModuleCat.Localization.closedSupportGEquiv.{u, u} f n).apply_symm_apply _
  have hl := PrincipalClosed.closedSupportGEquiv_globalSections R f n
    (Scheme.PrincipalClosed.boundaryG R f n a)
  have hm := closedBoundary_into_upperKernel R f n a
  have hn := DFunLike.congr_fun
    (SmallModelBoundaryNaturality.Universe.connectingHom_universe.{u + 1, u}
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f)) n)
        (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a)
  have hu := PrincipalClosed.publicGlobalSections_up
    (CommRingCat.of (Localization.Away f)) (n + 1) a
  exact hl.trans (hm.trans
    ((congrArg (SmallModelGLocalization.connectingHom.{u + 1}
      (FGModuleCat.localizationExactFunctor.{u, u} (Submonoid.powers f)) n) hu.symm).trans
        (hn.symm.trans (congrArg
          ((SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
            (FGModuleCat.localizationExactFunctor.{u, u}
              (Submonoid.powers f))).universalKMap n) hc.symm))))

end AlgebraicGeometry.Scheme.Modules.Coherent
