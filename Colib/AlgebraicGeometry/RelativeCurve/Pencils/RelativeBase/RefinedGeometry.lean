/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.BaseRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.MarkedCoordinate
/-! # The full compactification diagram after the simultaneous U/V refinement -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X C Y A Z D T : Scheme.{u}}
  (q : X ⟶ S) (U : X.Opens) (V : S.Opens)
  (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X) (hq : j ≫ π = p ≫ q)

include hq in
/-- The first source is restricted by the parameter, whereas C is restricted
only by the common base. This is the original refinement, not a smaller target. -/
def firstInclusion : firstSource q U V p ⟶ (compactificationOpen π V).toScheme :=
  IsOpenImmersion.lift (compactificationOpen π V).ι
    (pullback.fst p (parameterOpen q U V).ι ≫ j) (by
      rintro _ ⟨y, rfl⟩
      refine ⟨⟨j (pullback.fst p (parameterOpen q U V).ι y), ?_⟩, rfl⟩
      have hp := congrArg (fun f => f y) (pullback.condition (f := p)
        (g := (parameterOpen q U V).ι))
      change (j ≫ π) (pullback.fst p (parameterOpen q U V).ι y) ∈ V
      rw [hq]
      change q (p (pullback.fst p (parameterOpen q U V).ι y)) ∈ V
      simp only [Scheme.Hom.comp_apply] at hp
      rw [hp]
      exact (pullback.snd p (parameterOpen q U V).ι y).property.2)

@[reassoc (attr := simp)]
theorem firstInclusion_original :
    firstInclusion q U V π j p hq ≫ (compactificationOpen π V).ι =
      pullback.fst p (parameterOpen q U V).ι ≫ j := IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem firstInclusion_projection :
    firstInclusion q U V π j p hq ≫ compactificationProjection π V =
      firstMap q U V p ≫ parameterProjection q U V := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, compactificationProjection, morphismRestrict_ι,
    firstInclusion_original_assoc, hq, parameterProjection_base,
    firstMap, pullback.condition_assoc]

instance [IsOpenImmersion j] : IsOpenImmersion (firstInclusion q U V π j p hq) := by
  have : IsOpenImmersion (firstInclusion q U V π j p hq ≫ (compactificationOpen π V).ι) := by
    rw [firstInclusion_original]
    infer_instance
  exact IsOpenImmersion.of_comp (firstInclusion q U V π j p hq)
    (compactificationOpen π V).ι

instance [SmoothOfRelativeDimension 1 q] [Etale p] :
    SmoothOfRelativeDimension 1
      (firstInclusion q U V π j p hq ≫ compactificationProjection π V) := by
  rw [firstInclusion_projection]
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

variable (z : Z ⟶ X) (h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U)
  (s : Z ⟶ Y) (hs : s ≫ p = z)

/-- The complete mark in the base-restricted compactification is unchanged. -/
@[reassoc, simp]
theorem closedLift_inclusion_original :
    (closedLift q U V z h p s hs ≫ firstInclusion q U V π j p hq) ≫
        (compactificationOpen π V).ι = (markOpen q V z).ι ≫ s ≫ j := by
  simp only [Category.assoc, firstInclusion_original, closedLift_first_assoc]

/-- The closed mark is the entire Cartesian inverse image, including nilpotents. -/
theorem closedLift_inclusion_isPullback :
    IsPullback (closedLift q U V z h p s hs ≫ firstInclusion q U V π j p hq)
      (markOpen q V z).ι (compactificationOpen π V).ι (s ≫ j) := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (closedLift_inclusion_original q U V π j p hq z h s hs).symm
  ext b
  simp only [Scheme.Opens.opensRange_ι]
  change (s ≫ j ≫ π) b ∈ V ↔ (z ≫ q) b ∈ V
  rw [markedBase_eq q π j p hq z s hs]

instance [IsClosedImmersion (s ≫ j)] :
    IsClosedImmersion (closedLift q U V z h p s hs ≫ firstInclusion q U V π j p hq) :=
  MorphismProperty.of_isPullback
    (closedLift_inclusion_isPullback q U V π j p hq z h s hs).flip inferInstance

instance [IsFinite (z ≫ q)] :
    IsFinite ((closedLift q U V z h p s hs ≫ firstInclusion q U V π j p hq) ≫
      compactificationProjection π V) := by
  rw [Category.assoc, firstInclusion_projection, closedLift_parameter_assoc,
    markToParameter_base]
  infer_instance

/-- Infinity remains disjoint from the entire retained first open. -/
theorem refinedInfinity_disjoint (d : D ⟶ C)
    (hd : Disjoint (Set.range j) (Set.range d)) :
    Disjoint (Set.range (firstInclusion q U V π j p hq))
      (Set.range (sourceBaseMap π V d)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ ⟨b, hb⟩
  have he := congrArg (fun x => (compactificationOpen π V).ι x) hb
  change (sourceBaseMap π V d ≫ (compactificationOpen π V).ι) b =
    (firstInclusion q U V π j p hq ≫ (compactificationOpen π V).ι) y at he
  rw [sourceBaseMap_original, firstInclusion_original] at he
  exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩ he.symm

/-- The whole compactification is covered by the same retained target and both
full boundaries after base change. No parameter U is applied to the target. -/
theorem refinedBoundary_cover (d : D ⟶ C) (v : T ⟶ C)
    (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j)) :
    ∀ x : (compactificationOpen π V).toScheme,
      x ∈ Set.range (sourceBaseMap π V v) ∨
      x ∈ Set.range (sourceBaseMap π V d) ∨
      x ∈ Set.range (closedLift q U V z h p s hs ≫ firstInclusion q U V π j p hq) := by
  intro x
  rcases hc x.val with ⟨y, hy⟩ | ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    have hyV : (v ≫ π) y ∈ V := by change π (v y) ∈ V; rw [hy]; exact x.property
    refine ⟨⟨y, hyV⟩, ?_⟩
    apply (compactificationOpen π V).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨y, hyV⟩) (sourceBaseMap_original π V v)).trans hy
  · right; left
    have hbV : (d ≫ π) b ∈ V := by change π (d b) ∈ V; rw [hb]; exact x.property
    refine ⟨⟨b, hbV⟩, ?_⟩
    apply (compactificationOpen π V).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨b, hbV⟩) (sourceBaseMap_original π V d)).trans hb
  · right; right
    have hbV : (z ≫ q) b ∈ V := by
      rw [← markedBase_eq q π j p hq z s hs]
      change π ((s ≫ j) b) ∈ V
      rw [hb]
      exact x.property
    refine ⟨⟨b, hbV⟩, ?_⟩
    apply (compactificationOpen π V).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨b, hbV⟩)
      (closedLift_inclusion_original q U V π j p hq z h s hs)).trans hb

/-- The actual coefficient frame on the complete marked scheme, transported
without identifying the mark merely by its support. -/
def refinedMarkCoefficientFrame (L : C.Modules)
    (e : ((Modules.pullback (s ≫ j)).obj L).restrict (markOpen q V z).ι ≅
      SheafOfModules.unit (markOpen q V z).toScheme.ringCatSheaf) :
    (Modules.pullback (closedLift q U V z h p s hs ≫ firstInclusion q U V π j p hq)).obj
      (coefficientModule π V L) ≅ SheafOfModules.unit (markOpen q V z).toScheme.ringCatSheaf :=
  (Modules.pullbackComp _ (compactificationOpen π V).ι).app L ≪≫
    (Modules.pullbackCongr (closedLift_inclusion_original q U V π j p hq z h s hs)).app L ≪≫
    ((Modules.pullbackComp (markOpen q V z).ι (s ≫ j)).app L).symm ≪≫
    ((Modules.restrictFunctorIsoPullback (markOpen q V z).ι).app
      ((Modules.pullback (s ≫ j)).obj L)).symm ≪≫ e

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
