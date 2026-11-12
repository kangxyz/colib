/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.AffinePullback
public import Colib.AlgebraicGeometry.KTheory.CoherentAffineComparison
public import Colib.AlgebraicGeometry.KTheory.CoherentFlatPullback
public import Colib.Algebra.Category.ModuleCat.LocalizationTensor
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization

/-!
# Original affine G-pullback and finite-module localization

For an arbitrary multiplicative set in a Noetherian ring, the original public
coherent pullback corresponds to the actual finite-module localization map.
The ordinary square retains the native tilde counit and tensor universal
property; canonical small-model universe naturality gives the public square.

Implementation source:
`Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/LocalizationNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat

namespace AlgebraicGeometry.Scheme.Modules.Coherent

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- The actual spectrum map of a ring localization is flat. -/
instance localizationSpecMap_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S))

/-- Actual affine coherent pullback and actual global sections commute with module localization. -/
def coherentLocalizationGlobalSectionsIso :
    ((coherentExactPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).comp
        (affineGlobalSectionsExact (CommRingCat.of (Localization S)))).toFunctor ≅
      ((affineGlobalSectionsExact (CommRingCat.of R)).comp
        (FGModuleCat.localizationExactFunctor S)).toFunctor := by
  apply Functor.fullyFaithfulCancelRight
    (forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S)))
  exact coherentPullbackGlobalSectionsExtensionIso
      (CommRingCat.ofHom (algebraMap R (Localization S))) ≪≫
    Functor.isoWhiskerLeft
      ((affineGlobalSectionsExact (CommRingCat.of R)).toFunctor ⋙
        forget₂ (FGModuleCat R) (ModuleCat R))
      (ModuleCat.localizationTensorIso S)

/-- The original lower-model pullback K-map retains native finite-module localization. -/
theorem lowerPullbackG_globalSections_localization (n : ℕ) :
    ((affineGlobalSectionsExact (CommRingCat.of (Localization S))).smallKMap.{u} n).comp
      ((coherentExactPullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).smallKMap.{u} n) =
    (FGModuleCat.Localization.localizationKMap S n).comp
      ((affineGlobalSectionsExact (CommRingCat.of R)).smallKMap.{u} n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (coherentExactPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).comp
        (affineGlobalSectionsExact (CommRingCat.of (Localization S))))
    (G := (affineGlobalSectionsExact (CommRingCat.of R)).comp
      (FGModuleCat.localizationExactFunctor S))
    (coherentLocalizationGlobalSectionsIso S) n
  simpa only [ExactFunctor.smallKMap_comp,
    FGModuleCat.Localization.localizationKMap] using h

/-- The original public flat pullback agrees with native localization in every G-degree. -/
theorem publicSpecGRingEquiv_localization_pullback (n : ℕ) :
    (publicSpecGRingEquiv (CommRingCat.of (Localization S)) n).toMonoidHom.comp
      (Scheme.pullbackG
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n) =
    (FGModuleCat.Localization.localizationKMap S n).comp
      (publicSpecGRingEquiv (CommRingCat.of R) n).toMonoidHom := by
  let F := coherentExactPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))
  have hn := ExactFunctor.smallKUniverseEquiv_naturality.{u+1,u} F n
  ext a
  change specGRingEquiv (CommRingCat.of (Localization S)) n
      ((coherentExactStructure (Spec (CommRingCat.of (Localization S)))).smallKUniverseEquiv.{u+1,u}
        n (Scheme.pullbackG
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n a)) =
    FGModuleCat.Localization.localizationKMap S n
      (specGRingEquiv (CommRingCat.of R) n
        ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a))
  have ht := DFunLike.congr_fun
    (specGRingEquiv_eq_globalSectionsKMap (CommRingCat.of (Localization S)) n)
    ((coherentExactStructure (Spec (CommRingCat.of (Localization S)))).smallKUniverseEquiv.{u+1,u}
      n (Scheme.pullbackG
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n a))
  have hr := DFunLike.congr_fun
    (specGRingEquiv_eq_globalSectionsKMap (CommRingCat.of R) n)
    ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a)
  change specGRingEquiv (CommRingCat.of (Localization S)) n _ = _ at ht
  change specGRingEquiv (CommRingCat.of R) n _ = _ at hr
  rw [ht, hr]
  exact (congrArg ((affineGlobalSectionsExact (CommRingCat.of (Localization S))).smallKMap.{u} n)
    (DFunLike.congr_fun hn a).symm).trans
      (DFunLike.congr_fun (lowerPullbackG_globalSections_localization S n)
        ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a))

end AlgebraicGeometry.Scheme.Modules.Coherent
