/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentAffineSerreLocalization
public import Colib.KTheory.Quillen.Localization.SmallModelBoundaryNaturality

/-!
# Actual affine supported G-comparison

The global-sections square restricts to the genuine kernels of the original
geometric pullback and finite-module localization. The resulting K-equivalence
commutes with their original localization boundaries in the base universe.
This is not an equivalence of annihilated objects with all supported objects.

Implementation source: `Quillen/GTheory/SmallModelBoundaryNaturality.lean` and
`Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/PrincipalBoundaryComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- Global sections restricted to the actual small supported categories. -/
def supportedGlobalSectionsExact :=
  SmallModelBoundaryNaturality.Square.supportExact.{u}
    (affineLocalizationExact S) (FGModuleCat.localizationExactFunctor S)
    (affineGlobalSectionsExact (CommRingCat.of R))
    (affineGlobalSectionsExact (CommRingCat.of (Localization S)))
    (coherentLocalizationGlobalSectionsIso S)

/-- The canonical support functor is a K-equivalence. -/
def supportedGlobalSectionsKEquiv (n : ℕ) :
    SmallModelGLocalization.SupportedK.{u} (affineLocalizationExact S) n ≃*
      SmallModelGLocalization.SupportedK.{u} (FGModuleCat.localizationExactFunctor S) n := by
  have hR : (CategoryTheory.SmallModel.mapAbelianExactFunctor
      (affineGlobalSectionsExact (CommRingCat.of R))).toFunctor.IsEquivalence :=
    globalSectionsSmall_isEquivalence _
  have hS : (CategoryTheory.SmallModel.mapAbelianExactFunctor
      (affineGlobalSectionsExact (CommRingCat.of (Localization S)))).toFunctor.IsEquivalence :=
    globalSectionsSmall_isEquivalence _
  exact SmallModelBoundaryNaturality.Square.supportedKEquiv
    (affineLocalizationExact S) (FGModuleCat.localizationExactFunctor S)
    (affineGlobalSectionsExact (CommRingCat.of R))
    (affineGlobalSectionsExact (CommRingCat.of (Localization S)))
    (coherentLocalizationGlobalSectionsIso S) n

/-- The supported equivalence retains precisely the original restricted K-map. -/
theorem supportedGlobalSectionsKEquiv_toMonoidHom (n : ℕ) :
    (supportedGlobalSectionsKEquiv S n).toMonoidHom =
      (supportedGlobalSectionsExact S).KMap n := rfl

set_option maxHeartbeats 1000000 in
-- Elaborating the canonical small-model functor square unfolds both coherent and module models.
/-- The original connecting maps commute with actual supported global sections. -/
theorem supportedGlobalSections_connecting (n : ℕ) :
    ((supportedGlobalSectionsExact S).KMap n).comp
      (SmallModelGLocalization.connectingHom (affineLocalizationExact S) n) =
    (SmallModelGLocalization.connectingHom (FGModuleCat.localizationExactFunctor S) n).comp
      ((affineGlobalSectionsExact (CommRingCat.of (Localization S))).smallKMap.{u} (n + 1)) :=
  SmallModelBoundaryNaturality.Square.connecting_naturality
    (affineLocalizationExact S) (FGModuleCat.localizationExactFunctor S)
    (affineGlobalSectionsExact (CommRingCat.of R))
    (affineGlobalSectionsExact (CommRingCat.of (Localization S)))
    (coherentLocalizationGlobalSectionsIso S) n

/-- The actual global-sections equivalence also acts on the public upper small models. -/
instance upperGlobalSectionsSmall_isEquivalence
    (T : CommRingCat.{u}) [IsNoetherianRing T] :
    (CategoryTheory.SmallModel.mapAbelianExactFunctor.{u+1}
      (affineGlobalSectionsExact T)).toFunctor.IsEquivalence :=
  (((equivSmallModel.{u+1}
    (SheafOfModules.CoherentModules (Spec T).ringCatSheaf)).symm.trans
      (affineEquivalence T).symm).trans
        (equivSmallModel.{u+1} (FGModuleCat.{u} T))).isEquivalence_functor

/-- Actual supported global sections on the public upper small models. -/
def upperSupportedGlobalSectionsExact :=
  SmallModelBoundaryNaturality.Square.supportExact.{u+1}
    (affineLocalizationExact S) (FGModuleCat.localizationExactFunctor.{u,u} S)
    (affineGlobalSectionsExact (CommRingCat.of R))
    (affineGlobalSectionsExact (CommRingCat.of (Localization S)))
    (coherentLocalizationGlobalSectionsIso S)

/-- The upper support comparison retains the original restricted K-map. -/
def upperSupportedGlobalSectionsKEquiv (n : ℕ) :
    SmallModelGLocalization.SupportedK.{u+1} (affineLocalizationExact S) n ≃*
      SmallModelGLocalization.SupportedK.{u+1}
        (FGModuleCat.localizationExactFunctor.{u,u} S) n := by
  letI := upperGlobalSectionsSmall_isEquivalence (CommRingCat.of R)
  letI := upperGlobalSectionsSmall_isEquivalence (CommRingCat.of (Localization S))
  exact SmallModelBoundaryNaturality.Square.supportedKEquiv.{u+1}
    (affineLocalizationExact S) (FGModuleCat.localizationExactFunctor.{u,u} S)
    (affineGlobalSectionsExact (CommRingCat.of R))
    (affineGlobalSectionsExact (CommRingCat.of (Localization S)))
    (coherentLocalizationGlobalSectionsIso S) n

end AlgebraicGeometry.Scheme.Modules.Coherent
