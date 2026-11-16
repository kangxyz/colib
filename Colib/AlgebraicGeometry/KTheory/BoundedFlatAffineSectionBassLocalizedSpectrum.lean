/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescope
public import Colib.AlgebraicGeometry.KTheory.PerfectLocalizedPullback

/-!
# The initial map from affine perfect spectra to the Bass telescope

In the stable localization, invert the actual affine section evaluation and the literal
bounded-above-flat inclusion. Then take the original stage-zero map of the section Bass
telescope. Naturality uses derived pullback along every ring homomorphism, without flatness
of the ring map. This does not identify the classical negative Bass groups or prove
nonconnective localization.

The source comparison is `Affine/SectionBassLocalizedSpectrum.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The localized evaluation
inverse is the image of the actual chosen-zero-normalized inverse prespectrum map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The original perfect spectrum on affine schemes, covariant in the coefficient ring. -/
def affinePerfectLocalizedSpectrumFunctor : CommRingCat.{u} ⥤ StableLocalization.{u + 1} where
  obj R := perfectLocalizedSpectrum (Spec R)
  map f := perfectLocalizedPullback (Spec.map f)
  map_id R := by rw [Spec.map_id, perfectLocalizedPullback_id]
  map_comp f g := by rw [Spec.map_comp, perfectLocalizedPullback_comp]

/-- The actual section evaluation is inverted only in the stable localization. -/
def boundedAboveFlatAffineSectionEvaluationLocalizedIso (R : CommRingCat.{u}) :
    toStableLocalization.obj (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R) ≅
      boundedAboveFlatLocalizedSpectrum (Spec R) :=
  stableLocalizationIso (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R)

/-- The inverse in the localization is represented by the actual normalized prespectrum map. -/
@[colib_tag "COL-0362",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLocalizedComparison.lean:45-53"
    "adaptation" "The actual normalized evaluation inverse represents the localized inverse"]
theorem boundedAboveFlatAffineSectionEvaluationLocalizedIso_inv (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineSectionEvaluationLocalizedIso R).inv =
      toStableLocalization.map (boundedAboveFlatAffineEvaluationInversePrespectrumMap R) := by
  have h : Homotopy
      (boundedAboveFlatAffineEvaluationInversePrespectrumMap R ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap R) (𝟙 _) :=
    boundedAboveFlatAffineEvaluationRightHomotopy R
  apply (cancel_mono (boundedAboveFlatAffineSectionEvaluationLocalizedIso R).hom).mp
  rw [Iso.inv_hom_id]
  change 𝟙 _ = toStableLocalization.map (boundedAboveFlatAffineEvaluationInversePrespectrumMap R) ≫
    toStableLocalization.map (boundedAboveFlatAffineEvaluationPrespectrumMap R)
  rw [← Functor.map_comp, toStableLocalization_map_eq_of_homotopy h, Functor.map_id]

/-- The actual evaluation square commutes in the localization by the whole coefficient track. -/
@[reassoc]
theorem boundedAboveFlatAffineSectionEvaluationLocalizedIso_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    toStableLocalization.map (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) ≫
        (boundedAboveFlatAffineSectionEvaluationLocalizedIso S).hom =
      (boundedAboveFlatAffineSectionEvaluationLocalizedIso R).hom ≫
        boundedAboveFlatLocalizedPullback (Spec.map f) := by
  change toStableLocalization.map (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) ≫
      toStableLocalization.map (boundedAboveFlatAffineEvaluationPrespectrumMap S) =
    toStableLocalization.map (boundedAboveFlatAffineEvaluationPrespectrumMap R) ≫
      toStableLocalization.map (boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f))
  simp only [← Functor.map_comp]
  exact toStableLocalization_map_eq_of_homotopy
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f)

/-- The localized section spectrum computes the original perfect spectrum, naturally in rings. -/
def boundedAboveFlatAffineSectionPerfectLocalizedNatIso :
    boundedAboveFlatAffineSectionPrespectrumFunctor.{u} ⋙ toStableLocalization ≅
      affinePerfectLocalizedSpectrumFunctor :=
  NatIso.ofComponents
    (fun R ↦ boundedAboveFlatAffineSectionEvaluationLocalizedIso R ≪≫
      boundedAboveFlatPerfectSpectrumIso (Spec R))
    (fun {R S} f ↦ by
      change toStableLocalization.map (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) ≫
          ((boundedAboveFlatAffineSectionEvaluationLocalizedIso S).hom ≫
            (boundedAboveFlatPerfectSpectrumIso (Spec S)).hom) =
        ((boundedAboveFlatAffineSectionEvaluationLocalizedIso R).hom ≫
          (boundedAboveFlatPerfectSpectrumIso (Spec R)).hom) ≫ perfectLocalizedPullback (Spec.map f)
      simp only [Category.assoc,
        boundedAboveFlatAffineSectionEvaluationLocalizedIso_naturality_assoc,
        perfectLocalizedPullback_representatives])

/-- The actual affine section Bass telescope as a ring functor in the stable localization. -/
def boundedAboveFlatAffineSectionBassLocalizedSpectrumFunctor :
    CommRingCat.{u} ⥤ StableLocalization.{u + 1} :=
  boundedAboveFlatAffineSectionBassTelescopeFunctor ⋙ toStableLocalization

/-- Stage zero in the stable localization after the affine perfect comparison. -/
def affinePerfectBassTelescopeInitial :
    affinePerfectLocalizedSpectrumFunctor.{u} ⟶
      boundedAboveFlatAffineSectionBassLocalizedSpectrumFunctor :=
  boundedAboveFlatAffineSectionPerfectLocalizedNatIso.inv ≫
    Functor.whiskerRight boundedAboveFlatAffineSectionBassTelescopeInitial toStableLocalization

/-- The actual stage-zero map from the perfect spectrum of an affine scheme. -/
def affinePerfectBassTelescopeInitialMap (R : CommRingCat.{u}) :
    perfectLocalizedSpectrum (Spec R) ⟶
      toStableLocalization.obj (boundedAboveFlatAffineSectionBassTelescope R) :=
  affinePerfectBassTelescopeInitial.app R

/-- The map uses the unchanged inclusion inverse, normalized evaluation inverse and stage zero. -/
theorem affinePerfectBassTelescopeInitialMap_eq (R : CommRingCat.{u}) :
    affinePerfectBassTelescopeInitialMap R =
      (boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫
        toStableLocalization.map (boundedAboveFlatAffineEvaluationInversePrespectrumMap R ≫
          boundedAboveFlatAffineSectionBassTelescopeInitial.app R) := by
  change ((boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫
      (boundedAboveFlatAffineSectionEvaluationLocalizedIso R).inv) ≫
      toStableLocalization.map (boundedAboveFlatAffineSectionBassTelescopeInitial.app R) = _
  rw [Category.assoc, boundedAboveFlatAffineSectionEvaluationLocalizedIso_inv, Functor.map_comp]

/-- Starting with original section representatives recovers the actual initial face. -/
@[reassoc]
theorem affinePerfectBassTelescopeInitialMap_representatives (R : CommRingCat.{u}) :
    toStableLocalization.map (boundedAboveFlatAffineEvaluationPrespectrumMap R) ≫
        (boundedAboveFlatPerfectSpectrumIso (Spec R)).hom ≫
        affinePerfectBassTelescopeInitialMap R =
      toStableLocalization.map (boundedAboveFlatAffineSectionBassTelescopeInitial.app R) := by
  rw [affinePerfectBassTelescopeInitialMap_eq, Functor.map_comp,
    ← boundedAboveFlatAffineSectionEvaluationLocalizedIso_inv]
  change (boundedAboveFlatAffineSectionEvaluationLocalizedIso R).hom ≫
      (boundedAboveFlatPerfectSpectrumIso (Spec R)).hom ≫
      (boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫
      (boundedAboveFlatAffineSectionEvaluationLocalizedIso R).inv ≫ _ = _
  simp only [Iso.hom_inv_id_assoc]

/-- The map commutes with the actual derived pullback along every coefficient map. -/
@[reassoc]
theorem affinePerfectBassTelescopeInitialMap_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    perfectLocalizedPullback (Spec.map f) ≫ affinePerfectBassTelescopeInitialMap S =
      affinePerfectBassTelescopeInitialMap R ≫
        toStableLocalization.map (boundedAboveFlatAffineSectionBassTelescopeMap f) :=
  affinePerfectBassTelescopeInitial.naturality f

/-- Every signed stable map retains the two comparison inverses and the actual stage-zero map. -/
theorem affinePerfectBassTelescopeInitialMap_stable (R : CommRingCat.{u}) (d : ℤ) :
    (localizedStableHomotopyFunctor d).map (affinePerfectBassTelescopeInitialMap R) =
      (localizedStableHomotopyFunctor d).map (boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatAffineEvaluationInversePrespectrumMap R) ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatAffineSectionBassTelescopeInitial.app R) := by
  simp only [affinePerfectBassTelescopeInitialMap_eq, Functor.map_comp,
    localizedStableHomotopyFunctor_original_map]

/-- In every nonnegative degree this is natural for the original perfect K-map. -/
theorem affinePerfectBassTelescopeInitialMap_originalK_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (a : (perfectComplexesWaldhausen (Spec R).toRingedSpace).K n) :
    (localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap S)
        (originalKStableEquiv (perfectComplexesWaldhausen (Spec S).toRingedSpace) n
          (Additive.ofMul (perfectKPullback (Spec.map f) n a))) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedAboveFlatAffineSectionBassTelescopeMap f)
        ((localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) n
            (Additive.ofMul a))) := by
  have h := congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map)
    (affinePerfectBassTelescopeInitialMap_naturality f)
  simp only [Functor.map_comp, localizedStableHomotopyFunctor_original_map] at h
  exact (congrArg
    ((localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap S))
    (perfectLocalizedPullback_originalK_naturality (Spec.map f) n a)).trans
      (ConcreteCategory.congr_hom h
        (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) n
          (Additive.ofMul a)))

attribute [colib_tag "COL-0362",
  colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassLocalizedSpectrum.lean:24-113"
  "adaptation" "The original affine perfect spectrum maps to the actual localized Bass \
    telescope, using the original normalized evaluation inverse and stage-zero face."]
  affinePerfectBassTelescopeInitial affinePerfectBassTelescopeInitialMap
  affinePerfectBassTelescopeInitialMap_eq affinePerfectBassTelescopeInitialMap_representatives
  affinePerfectBassTelescopeInitialMap_naturality affinePerfectBassTelescopeInitialMap_stable
  affinePerfectBassTelescopeInitialMap_originalK_naturality

end AlgebraicGeometry.Scheme.Modules
