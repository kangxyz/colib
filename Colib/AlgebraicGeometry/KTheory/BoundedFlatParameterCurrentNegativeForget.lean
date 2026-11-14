/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAmbientCurrentNegativeComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentStageRange
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterTelescopeForget
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeSquares
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeForgetComparison

/-!
# Original support forgetting in the current negative groups

The original supported negative-group map commutes with the finite comparison
and the independent current inclusion. The proof uses the original finite
forgetting squares, without cancelling a support-forgetting map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection SchemeNaturalSeed ParameterLaurentTrack

private theorem inverse_class_square {C : Type*} [Category C]
    {A B S T S' T' S'' T'' : C}
    (a : A ⟶ B) (g : A ⟶ S) (h : B ⟶ T) (f : S ⟶ T)
    (v : S' ⟶ S) (w : T' ⟶ T) (f' : S' ⟶ T')
    (e : S'' ⟶ S') (k : T'' ⟶ T') (f'' : S'' ⟶ T'')
    [IsIso v] [IsIso w] [IsIso e] [IsIso k]
    (h₀ : a ≫ h = g ≫ f) (h₁ : v ≫ f = f' ≫ w) (h₂ : e ≫ f' = f'' ≫ k) :
    a ≫ (h ≫ inv w ≫ inv k) = (g ≫ inv v ≫ inv e) ≫ f'' := by
  have hv : f ≫ inv w = inv v ≫ f' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, h₁]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have he : f' ≫ inv k = inv e ≫ f'' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, h₂]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  calc
    a ≫ (h ≫ inv w ≫ inv k) = g ≫ (f ≫ inv w) ≫ inv k := by
      rw [← Category.assoc a h, h₀]
      simp only [Category.assoc]
    _ = g ≫ (inv v ≫ f') ≫ inv k := by rw [hv]
    _ = (g ≫ inv v) ≫ (f' ≫ inv k) := by simp only [Category.assoc]
    _ = (g ≫ inv v) ≫ (inv e ≫ f'') := by rw [he]
    _ = (g ≫ inv v ≫ inv e) ≫ f'' := by simp only [Category.assoc]

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The unchanged finite supported comparison preserves original support forgetting. -/
@[reassoc]
theorem finiteNegativeKComparison_forget (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (GlobalParameterCoefficient.finiteNegativeKComparison Q i).hom.app a =
    (finiteNegativeKComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((((strictDiagramIterate squareFunctor i).map
          (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor))).app
            (specUnder.obj a)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let : IsIso (H.map ((SupportedTelescope.finiteRestriction f i).app a)) :=
    SupportedTelescope.finiteRestriction_isStableEquivalence f i a (-(i : ℤ))
  let : IsIso (H.map ((GlobalSectionChangeIndex.finiteRestriction Q i).app a)) :=
    GlobalSectionChangeIndex.finiteRestriction_isStableEquivalence Q i a (-(i : ℤ))
  have h₁ := congrArg (fun η => H.map (η.app a))
    (LocalizationTelescope.finiteForget_square f i)
  have h₂ := congrArg (fun η => H.map (η.app a)) (finite_forget_square f i)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp] at h₁ h₂
  rw [finiteNegativeKComparison_hom_app,
    GlobalParameterCoefficient.finiteNegativeKComparison_hom_app]
  simpa only [← Functor.map_inv, NatIso.inv_hom_app] using
    inverse_class_square _ _ _ _ _ _ _ _ _ _
    (boundedAboveFlatCoefficientSupportedNegativeKComparison_forget_app f i a) h₁ h₂.symm

variable [CompactSpace P.left] [QuasiSeparatedSpace Q.left]

omit [CompactSpace Q.left] [CompactSpace P.left] [QuasiSeparatedSpace Q.left] in
/-- The actual current supported inclusion commutes with the original current forgetful map. -/
theorem currentStageInclusion_forget (i : ℕ) :
    currentStageInclusion f i ≫
      currentInputMap (supportedTrack f.left) (ambientTrack Q.left)
        (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor)
        (forget_equivariant f.left) =
    (strictDiagramIterate squareFunctor i).map
        (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor) ≫
      GlobalParameterCoefficient.currentStageInclusion Q i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Every original negative support-forgetting arrow is retained in the current telescope. -/
@[reassoc]
theorem currentNegativeKComparison_forget (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (GlobalParameterCoefficient.currentNegativeKComparison Q i).hom.app a =
    (currentNegativeKComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((currentInputMap (supportedTrack f.left) (ambientTrack Q.left)
          (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor)
          (forget_equivariant f.left)).app (specUnder.obj a)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  have h := congrArg (fun η => H.map (η.app (specUnder.obj a)))
    (currentStageInclusion_forget f i)
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [currentNegativeKComparison_hom_app,
    GlobalParameterCoefficient.currentNegativeKComparison_hom_app,
    ← Category.assoc, finiteNegativeKComparison_forget]
  simpa only [Category.assoc] using
    congrArg (fun k => (finiteNegativeKComparison f i).hom.app a ≫ k) h.symm

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
