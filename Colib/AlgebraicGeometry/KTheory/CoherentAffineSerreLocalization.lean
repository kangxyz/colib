/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentAffineLocalization
public import Colib.CategoryTheory.SmallModel.Localization

/-!
# The original affine coherent localization is a Serre localization

The actual affine global-sections equivalences and the original localization
square transport the native finite-module Serre localization. The resulting
morphism property is that of the kernel of the actual coherent pullback, not a
replacement category or an unspecified support term.
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

instance coherentLocalization_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))) := by
  let F := coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))
  let J := affineGlobalSections (CommRingCat.of (Localization S))
  have : J.IsEquivalence := affineGlobalSections_isEquivalence _
  have : (affineGlobalSections (CommRingCat.of R)).IsEquivalence :=
    affineGlobalSections_isEquivalence _
  have : PreservesFiniteLimits
      ((affineGlobalSectionsExact (CommRingCat.of R)).comp
        (FGModuleCat.localizationExactFunctor S)).toFunctor := by
    change PreservesFiniteLimits
      (affineGlobalSections (CommRingCat.of R) ⋙ FGModuleCat.localizedModuleFunctor S)
    exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (F ⋙ J) :=
    preservesFiniteLimits_of_natIso (coherentLocalizationGlobalSectionsIso S).symm
  exact preservesFiniteLimits_of_reflects_of_preserves F J

instance coherentLocalization_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))) := by
  let F := coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))
  let J := affineGlobalSections (CommRingCat.of (Localization S))
  have : J.IsEquivalence := affineGlobalSections_isEquivalence _
  have : (affineGlobalSections (CommRingCat.of R)).IsEquivalence :=
    affineGlobalSections_isEquivalence _
  have : PreservesFiniteColimits
      ((affineGlobalSectionsExact (CommRingCat.of R)).comp
        (FGModuleCat.localizationExactFunctor S)).toFunctor := by
    change PreservesFiniteColimits
      (affineGlobalSections (CommRingCat.of R) ⋙ FGModuleCat.localizedModuleFunctor S)
    exact comp_preservesFiniteColimits _ _
  have : PreservesFiniteColimits (F ⋙ J) :=
    preservesFiniteColimits_of_natIso (coherentLocalizationGlobalSectionsIso S).symm
  exact preservesFiniteColimits_of_reflects_of_preserves F J

/-- The original coherent pullback localizes at the Serre isomorphisms of its actual kernel. -/
instance coherentLocalization_isLocalization :
    (coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).IsLocalization
      (coherentPullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).kernel.isoModSerre := by
  let F := coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))
  let G := FGModuleCat.localizedModuleFunctor S
  let E := affineEquivalence (CommRingCat.of R)
  let E' := affineEquivalence (CommRingCat.of (Localization S))
  let L := G ⋙ E'.functor
  let W := (FGModuleCat.localizationTorsionProperty S).isoModSerre
  have : G.IsLocalization W := FGModuleCat.localizedModuleFunctor_isLocalization S
  have e : E.functor ⋙ F ≅ L :=
    Functor.fullyFaithfulCancelRight E'.inverse
      (Functor.isoWhiskerLeft E.functor (coherentLocalizationGlobalSectionsIso S) ≪≫
        Functor.isoWhiskerRight E.unitIso.symm G ≪≫
        Functor.isoWhiskerLeft G E'.unitIso)
  have hinv : F.kernel.isoModSerre.IsInvertedBy F := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro X Y f hf
    exact hf
  apply Functor.IsLocalization.of_equivalence_source L W
    F F.kernel.isoModSerre E ?_ hinv e
  have hi : W.IsInvertedBy (E.functor ⋙ F) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ e).2
      (CategoryTheory.Localization.inverts L W)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- The actual coherent localization exact functor. -/
abbrev affineLocalizationExact :=
  coherentExactPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))

instance affineLocalizationExact_preservesFiniteLimits :
    PreservesFiniteLimits (affineLocalizationExact S).toFunctor :=
  coherentLocalization_preservesFiniteLimits S

instance affineLocalizationExact_preservesFiniteColimits :
    PreservesFiniteColimits (affineLocalizationExact S).toFunctor :=
  coherentLocalization_preservesFiniteColimits S

instance affineLocalizationExact_isLocalization :
    (affineLocalizationExact S).toFunctor.IsLocalization
      (affineLocalizationExact S).toFunctor.kernel.isoModSerre :=
  coherentLocalization_isLocalization S

end AlgebraicGeometry.Scheme.Modules.Coherent
