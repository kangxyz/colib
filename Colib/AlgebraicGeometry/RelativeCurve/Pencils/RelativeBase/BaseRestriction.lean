/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.Diagram
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
/-! # Literal base-only restrictions of the compactification and retained target -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S C E : Scheme.{u}} (π : C ⟶ S) (V : S.Opens)

/-- The complete compactification over V; the parameter neighborhood does not enter. -/
abbrev compactificationOpen : C.Opens := π ⁻¹ᵁ V

/-- The original proper projection restricted to the actual common base. -/
abbrev compactificationProjection : (compactificationOpen π V).toScheme ⟶ V.toScheme := π ∣_ V

/-- The entire source of a boundary or retained-target map over V. -/
abbrev sourceBaseOpen (f : E ⟶ C) : E.Opens := (f ≫ π) ⁻¹ᵁ V

/-- The actual source map into the base-restricted compactification. -/
def sourceBaseMap (f : E ⟶ C) :
    (sourceBaseOpen π V f).toScheme ⟶ (compactificationOpen π V).toScheme :=
  IsOpenImmersion.lift (compactificationOpen π V).ι
    ((sourceBaseOpen π V f).ι ≫ f) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨f x.val, x.property⟩, rfl⟩)

@[reassoc (attr := simp)]
theorem sourceBaseMap_original (f : E ⟶ C) :
    sourceBaseMap π V f ≫ (compactificationOpen π V).ι =
      (sourceBaseOpen π V f).ι ≫ f := IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem sourceBaseMap_projection (f : E ⟶ C) :
    sourceBaseMap π V f ≫ compactificationProjection π V = (f ≫ π) ∣_ V := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, compactificationProjection, morphismRestrict_ι,
    sourceBaseMap_original_assoc]

/-- The full source, with all of its scheme structure, is Cartesian. -/
theorem sourceBaseMap_isPullback (f : E ⟶ C) :
    IsPullback (sourceBaseMap π V f) (sourceBaseOpen π V f).ι
      (compactificationOpen π V).ι f := by
  apply IsOpenImmersion.isPullback _ _ _ _ (sourceBaseMap_original π V f).symm
  ext x
  simp only [Scheme.Opens.opensRange_ι]
  rfl

instance (f : E ⟶ C) [IsOpenImmersion f] : IsOpenImmersion (sourceBaseMap π V f) :=
  MorphismProperty.of_isPullback (sourceBaseMap_isPullback π V f).flip inferInstance

instance (f : E ⟶ C) [IsClosedImmersion f] : IsClosedImmersion (sourceBaseMap π V f) :=
  MorphismProperty.of_isPullback (sourceBaseMap_isPullback π V f).flip inferInstance

instance (f : E ⟶ C) [IsFinite (f ≫ π)] :
    IsFinite (sourceBaseMap π V f ≫ compactificationProjection π V) := by
  rw [sourceBaseMap_projection]
  infer_instance

instance (f : E ⟶ C) [SmoothOfRelativeDimension 1 (f ≫ π)] :
    SmoothOfRelativeDimension 1 (sourceBaseMap π V f ≫ compactificationProjection π V) := by
  rw [sourceBaseMap_projection]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (isPullback_morphismRestrict (f ≫ π) V).flip
    (inferInstance : SmoothOfRelativeDimension 1 (f ≫ π))

/-- Affineness of the retained source uses both affine bases, not just quasi-affineness. -/
theorem sourceBaseOpen_affine [IsAffine E] [IsAffine S] (f : E ⟶ C)
    (hV : IsAffineOpen V) : IsAffineOpen (sourceBaseOpen π V f) :=
  hV.preimage (f ≫ π)

/-- The actual pulled coefficient module on the full relative compactification. -/
abbrev coefficientModule (L : C.Modules) : (compactificationOpen π V).toScheme.Modules :=
  (Modules.pullback (compactificationOpen π V).ι).obj L

/-- The restriction map is affine because it is the base change of V into S. -/
theorem compactificationOpen_isAffineHom [IsAffine S] (hV : IsAffineOpen V) :
    IsAffineHom (compactificationOpen π V).ι := by
  let : IsAffine V.toScheme := hV
  exact isAffineHom_isStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict π V) (isAffineHom_of_isAffine V.ι)

set_option maxHeartbeats 400000 in
-- The ampleness comparison uses the scheme and ringed-space pullback spellings.
/-- Pulling the actual ample module along this affine base change stays ample. -/
theorem coefficientModule_isAmple [IsAffine S] (hV : IsAffineOpen V)
    (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L) :
    IsAmple (compactificationOpen π V).toScheme (coefficientModule π V L) := by
  let : IsAffineHom (compactificationOpen π V).ι := compactificationOpen_isAffineHom π V hV
  exact Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (compactificationOpen π V).ι L hL

/-- A genuine whole-boundary frame is transported with the actual maps and
native pullback associator. No fibre-only trivialization is substituted. -/
def coefficientFrame (f : E ⟶ C) (L : C.Modules)
    (e : ((Modules.pullback f).obj L).restrict (sourceBaseOpen π V f).ι ≅
      SheafOfModules.unit (sourceBaseOpen π V f).toScheme.ringCatSheaf) :
    (Modules.pullback (sourceBaseMap π V f)).obj (coefficientModule π V L) ≅
      SheafOfModules.unit (sourceBaseOpen π V f).toScheme.ringCatSheaf :=
  (Modules.pullbackComp (sourceBaseMap π V f) (compactificationOpen π V).ι).app L ≪≫
    (Modules.pullbackCongr (sourceBaseMap_original π V f)).app L ≪≫
    ((Modules.pullbackComp (sourceBaseOpen π V f).ι f).app L).symm ≪≫
    ((Modules.restrictFunctorIsoPullback (sourceBaseOpen π V f).ι).app
      ((Modules.pullback f).obj L)).symm ≪≫ e

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
