/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentNegativeCorrection
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientNegativeLocalizationBoundary
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFineConnectingComparison

/-!
# The actual negative boundary and its finite corrections

The intrinsic current boundary is transported through the unchanged original
current negative classes. It intertwines the actual finite-word corrections
with the existing signed boundary on the original negative groups, including
its integer-degree casts. Equality of the two boundaries is equivalent to the
corrections commuting with the original boundary.

For N₁ to N₂ this condition only asks that the original boundary be fixed by
the second supported correction. It does not assume that correction is trivial
on the entire supported group or that a variable swap acts by a scalar sign.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex KTheory.Bass.SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

private theorem stable_degree_comparison
    (O S : Topology.LoopPrespectrum.{u + 1})
    (e : ∀ d : ℤ, stableHomotopyGroup O d ≅ stableHomotopyGroup S d)
    {d d' : ℤ} (h : d = d') :
    (eqToIso (congrArg stableHomotopyFunctor h)).hom.app O ≫ (e d').hom =
      (e d).hom ≫ (eqToIso (congrArg stableHomotopyFunctor h)).hom.app S := by
  subst d'
  change 𝟙 _ ≫ (e d).hom = (e d).hom ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

private theorem correction_boundary_square {C : Type*} [Category C]
    {A B D E F G : C} (x : A ⟶ B) (x' : A ⟶ D)
    (y : E ≅ F) (y' : E ≅ G) (c : A ≅ A) (c' : E ≅ E)
    (g : B ⟶ D) (h : F ⟶ G) (δ : B ⟶ F) (δ' : D ⟶ G)
    (hx : x ≫ g = c.hom ≫ x') (hy : y.hom ≫ h = c'.hom ≫ y'.hom)
    (hδ : δ ≫ h = g ≫ δ') :
    (x ≫ δ ≫ y.inv) ≫ c'.hom = c.hom ≫ (x' ≫ δ' ≫ y'.inv) := by
  apply (cancel_mono y'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hy, Iso.inv_hom_id_assoc, hδ, ← Category.assoc, hx]
  simp only [Category.assoc]

/-- The intrinsic current boundary through the unchanged original negative classes. -/
def currentNegativeConnecting (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.negativeKFunctor i).obj ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) ⟶
      (Bass.supportedNegativeKFunctor (i + 1)).obj
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact (GlobalParameterCoefficient.currentNegativeKComparison P i).hom.app a ≫
    (negativeLocalizationDegreeIso i).hom.app
      ((currentTelescope (ParameterLaurentTrack.ambientTrack P.left)).obj (specUnder.obj a)) ≫
    currentConnecting f a (-((i + 1 : ℕ) : ℤ)) ≫
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison f (i + 1)).inv.app a

set_option maxHeartbeats 600000 in
-- Both degree casts retain the actual fine and current spectrum endpoints.
/-- The actual current boundary intertwines the actual finite corrections with the
original signed boundary, retaining the original integer-degree transports. -/
@[reassoc]
theorem currentNegativeConnecting_correction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
    currentNegativeConnecting f i a ≫
        (GlobalSupportedParameterCoefficient.negativeClassCorrection f (i + 1) a).hom =
      (GlobalParameterCoefficient.negativeClassCorrection P i a).hom ≫
        boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  have hx : (GlobalParameterCoefficient.currentNegativeKComparison P i).hom.app a ≫
      (currentFineOpenComparison f a (-(i : ℤ))).hom =
      (GlobalParameterCoefficient.negativeClassCorrection P i a).hom ≫
        (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a :=
    GlobalParameterCoefficient.currentNegativeKComparison_fine_correction P i a
  have hy : (GlobalSupportedParameterCoefficient.currentNegativeKComparison f (i + 1)).hom.app a ≫
      (currentFineSupportComparison f a (-((i + 1 : ℕ) : ℤ))).hom =
      (GlobalSupportedParameterCoefficient.negativeClassCorrection f (i + 1) a).hom ≫
        (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).hom.app a :=
    GlobalSupportedParameterCoefficient.currentNegativeKComparison_fine_correction f (i + 1) a
  have hd : (negativeLocalizationDegreeIso i).hom.app
        ((currentTelescope (ParameterLaurentTrack.ambientTrack P.left)).obj (specUnder.obj a)) ≫
      (currentFineOpenComparison f a (-((i + 1 : ℕ) : ℤ) + 1)).hom =
      (currentFineOpenComparison f a (-(i : ℤ))).hom ≫
        (negativeLocalizationDegreeIso i).hom.app
          ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) :=
    stable_degree_comparison
      ((currentTelescope (ParameterLaurentTrack.ambientTrack P.left)).obj (specUnder.obj a))
      ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)
      (currentFineOpenComparison f a)
      (d := -(i : ℤ)) (d' := -((i + 1 : ℕ) : ℤ) + 1) (by omega)
  have hx' := congrArg (fun z => z ≫ (negativeLocalizationDegreeIso i).hom.app
    ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)) hx
  simp only [Category.assoc] at hx'
  rw [← hd] at hx'
  have h := correction_boundary_square
    ((GlobalParameterCoefficient.currentNegativeKComparison P i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((currentTelescope (ParameterLaurentTrack.ambientTrack P.left)).obj (specUnder.obj a)))
    ((boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a))
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison f (i + 1)).app a)
    ((boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).app a)
    (GlobalParameterCoefficient.negativeClassCorrection P i a)
    (GlobalSupportedParameterCoefficient.negativeClassCorrection f (i + 1) a)
    (currentFineOpenComparison f a (-((i + 1 : ℕ) : ℤ) + 1)).hom
    (currentFineSupportComparison f a (-((i + 1 : ℕ) : ℤ))).hom
    (currentConnecting f a (-((i + 1 : ℕ) : ℤ)))
    (boundedAboveFlatCoefficientFineLocalizationConnecting f a (-((i + 1 : ℕ) : ℤ)))
    (by simpa only [Category.assoc] using hx') hy
    (current_fine_connecting f a (-((i + 1 : ℕ) : ℤ)))
  simpa only [currentNegativeConnecting, boundedAboveFlatCoefficientNegativeLocalizationConnecting,
    Iso.app_inv, Category.assoc] using h

/-- Equality with the original boundary is precisely the finite-correction square. -/
theorem currentNegativeConnecting_eq_original_iff (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
    currentNegativeConnecting f i a =
        boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a ↔
      boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a ≫
          (GlobalSupportedParameterCoefficient.negativeClassCorrection f (i + 1) a).hom =
        (GlobalParameterCoefficient.negativeClassCorrection P i a).hom ≫
          boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  constructor
  · intro h
    simpa only [h] using currentNegativeConnecting_correction f i a
  · intro h
    apply (cancel_mono
      (GlobalSupportedParameterCoefficient.negativeClassCorrection f (i + 1) a).hom).1
    exact (currentNegativeConnecting_correction f i a).trans h.symm

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
