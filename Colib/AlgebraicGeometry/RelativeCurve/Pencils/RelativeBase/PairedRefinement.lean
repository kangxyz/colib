/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CanonicalFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedBoundaryFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedSectionData
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedGeometry

/-!
# The two normalized pairs on a common coefficient restriction

The retained parameter is the whole original relative curve over one
principal coefficient open. Its source and target compactifications use
that same open, with the original entire marks and boundary schemes.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Common/OriginalOverlapSectionChoice.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X C : Scheme.{u}} (q : X ⟶ S) (V : S.Opens)
  (π : C ⟶ S) (j : X ⟶ C) (hj : j ≫ π = (𝟙 X) ≫ q)

/-- The original target inclusion on the restricted parameter, with no
change of the chosen parameter object. -/
def targetInclusion :
    (parameterOpen q ⊤ V).toScheme ⟶ (compactificationOpen π V).toScheme :=
  inv (firstMap q ⊤ V (𝟙 X)) ≫ firstInclusion q ⊤ V π j (𝟙 X) hj

instance targetInclusion_open [IsOpenImmersion j] :
    IsOpenImmersion (targetInclusion q V π j hj) := by
  unfold targetInclusion
  infer_instance

/-- The original inclusion from the parameter open identifies the new target. -/
@[reassoc (attr := simp)]
theorem targetInclusion_original :
    targetInclusion q V π j hj ≫ (compactificationOpen π V).ι =
      (parameterOpen q ⊤ V).ι ≫ j := by
  have hp : pullback.fst (𝟙 X) (parameterOpen q ⊤ V).ι =
      firstMap q ⊤ V (𝟙 X) ≫ (parameterOpen q ⊤ V).ι := by
    simpa only [Category.comp_id] using
      (pullback.condition (f := 𝟙 X) (g := (parameterOpen q ⊤ V).ι))
  rw [targetInclusion, Category.assoc, firstInclusion_original, hp,
    Category.assoc, IsIso.inv_hom_id_assoc]

/-- The original retained square commutes after the common coefficient
restriction, with the literal base change of the compactification map. -/
theorem firstInclusion_comp_coefficientMap {B Y : Scheme.{u}}
    (f : B ⟶ C) (jB : Y ⟶ B) (p : Y ⟶ X) (h : jB ≫ f = p ≫ j)
    (hq : jB ≫ (f ≫ π) = p ≫ q) :
    firstInclusion q ⊤ V (f ≫ π) jB p hq ≫ sourceBaseMap π V f =
      firstMap q ⊤ V p ≫ targetInclusion q V π j hj := by
  apply (cancel_mono (compactificationOpen π V).ι).mp
  simp only [Category.assoc, sourceBaseMap_original, firstInclusion_original_assoc,
    targetInclusion_original, h, firstMap, pullback.condition_assoc]

/-- The actual projection on the target is the restricted parameter projection. -/
theorem targetInclusion_projection :
    targetInclusion q V π j hj ≫ compactificationProjection π V =
      (𝟙 _) ≫ parameterProjection q ⊤ V := by
  rw [targetInclusion, Category.assoc, firstInclusion_projection, IsIso.inv_hom_id_assoc,
    Category.id_comp]

instance targetInclusion_smooth [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1
      (targetInclusion q V π j hj ≫ compactificationProjection π V) := by
  rw [targetInclusion_projection, Category.id_comp]
  infer_instance

/-- On the mark the target inclusion uses the same actual restriction as the
identity first-source diagram. -/
theorem targetInclusion_mark {Z : Scheme.{u}} (z : Z ⟶ X) :
    markToParameter q ⊤ V z (fun _ _ ↦ trivial) ≫ targetInclusion q V π j hj =
      closedLift q ⊤ V z (fun _ _ ↦ trivial) (𝟙 X) z (Category.comp_id z) ≫
        firstInclusion q ⊤ V π j (𝟙 X) hj := by
  rw [targetInclusion, ← closedLift_parameter q ⊤ V z (fun _ _ ↦ trivial) (𝟙 X)
    z (Category.comp_id z), Category.assoc, IsIso.hom_inv_id_assoc]

/-- The actual restriction of the retained target stays disjoint from the
entire base-restricted boundary. -/
theorem targetInclusion_disjoint {D : Scheme.{u}} (d : D ⟶ C)
    (hd : Disjoint (Set.range j) (Set.range d)) :
    Disjoint (Set.range (targetInclusion q V π j hj)) (Set.range (sourceBaseMap π V d)) := by
  apply Set.disjoint_left.2
  rintro _ ⟨x, rfl⟩ hx
  exact Set.disjoint_left.1 (refinedInfinity_disjoint q ⊤ V π j (𝟙 X) hj d hd)
    ⟨inv (firstMap q ⊤ V (𝟙 X)) x, rfl⟩ hx

section Pair

variable {Y A Z C' D₁ D₂ : Scheme.{u}} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π₁ : C ⟶ S} [IsSeparated π₁] (j₁ : Y ⟶ C) [IsOpenImmersion j₁]
  (p : Y ⟶ X) [Etale p]
  (hq₁ : j₁ ≫ π₁ = p ≫ q)
  {π₂ : C' ⟶ S} [IsSeparated π₂] (j₂ : X ⟶ C') [IsOpenImmersion j₂]
  (hq₂ : j₂ ≫ π₂ = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a] (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j₁) (Set.range d₁))
  (d₂ : D₂ ⟶ C') (hd₂ : Disjoint (Set.range j₂) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))

local notation "q'" => (parameterProjection q ⊤ V)
local notation "π₁'" => (compactificationProjection π₁ V)
local notation "π₂'" => (compactificationProjection π₂ V)
local notation "j₁'" => (firstInclusion q ⊤ V π₁ j₁ p hq₁)
local notation "j₂'" => (targetInclusion q V π₂ j₂ hq₂)
local notation "p'" => (firstMap q ⊤ V p)
local notation "a'" => (secondMap q ⊤ V a)
local notation "z'" => (markToParameter q ⊤ V z (fun _ _ ↦ trivial))
local notation "s'" => (closedLift q ⊤ V z (fun _ _ ↦ trivial) p s hs)
local notation "d₁'" => (sourceBaseMap π₁ V d₁)
local notation "d₂'" => (sourceBaseMap π₂ V d₂)

/-- The actual source and target section pairs after restricting only the
coefficient base. -/
def PairedSectionDataOnCoefficientOpen : Prop :=
  ∃ e : divisorSheaf (relativeBoundaryGraph q' z').ker ≅
      SheafOfModules.unit (pullback q' (z' ≫ q')).ringCatSheaf,
    Nonempty (SectionData q' π₁' j₁' p'
        (firstInclusion_projection q ⊤ V π₁ j₁ p hq₁) a' z' s'
        (closedLift_parameter q ⊤ V z (fun _ _ ↦ trivial) p s hs)
        (closedLift_isPullback q ⊤ V z (fun _ _ ↦ trivial) p s hs H) e d₁'
        (refinedInfinity_disjoint q ⊤ V π₁ j₁ p hq₁ d₁ hd₁)
        (puncture_disjoint q ⊤ V z (fun _ _ ↦ trivial) a ha) ×
      SectionData q' π₂' j₂' (𝟙 _) (targetInclusion_projection q V π₂ j₂ hq₂)
        a' z' z' (Category.comp_id z') (IsPullback.of_id_snd (f := z')) e d₂'
        (targetInclusion_disjoint q V π₂ j₂ hq₂ d₂ hd₂)
        (puncture_disjoint q ⊤ V z (fun _ _ ↦ trivial) a ha))

omit V [IsSeparated π₁] [IsSeparated π₂] in
/-- One actual principal coefficient neighborhood supplies both normalized
pairs, retaining all original points of the mark and the two boundaries. -/
theorem exists_pairedSectionData_on_coefficientOpen
    [IsAffine S] [IsLocallyNoetherian S] [IsAffine X] [IsAffine Y] [IsAffine A]
    [IsProper π₁] [IsProper π₂] [IsFinite (z ≫ q)]
    [IsClosedImmersion (s ≫ j₁)] [IsClosedImmersion (z ≫ j₂)]
    [IsClosedImmersion d₁] [IsClosedImmersion d₂]
    [IsFinite (d₁ ≫ π₁)] [IsFinite (d₂ ≫ π₂)]
    (e₀ : divisorSheaf (relativeBoundaryGraph q z).ker ≅
      SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
    (L₁ : C.Modules) [IsInvertibleModule C L₁] (hL₁ : IsAmple C L₁)
    (L₂ : C'.Modules) [IsInvertibleModule C' L₂] (hL₂ : IsAmple C' L₂)
    (W : S.Opens) (x : S) (hxW : x ∈ W) :
    letI : IsSeparated π₁ := ‹IsProper π₁›.toIsSeparated
    letI : IsSeparated π₂ := ‹IsProper π₂›.toIsSeparated
    ∃ r : Γ(S, ⊤), x ∈ S.basicOpen r ∧ S.basicOpen r ≤ W ∧
      PairedSectionDataOnCoefficientOpen q (S.basicOpen r) j₁ p hq₁ j₂ hq₂
        a z s hs H d₁ hd₁ d₂ hd₂ ha := by
  obtain ⟨r, hxr, hrW, ⟨eD₁⟩, ⟨eZ₁⟩, ⟨eD₂⟩, ⟨eZ₂⟩⟩ :=
    exists_commonPrincipalPairedBoundaryFrames (d₁ ≫ π₁) (z ≫ q) (d₂ ≫ π₂) (z ≫ q)
      ((Modules.pullback d₁).obj L₁) ((Modules.pullback (s ≫ j₁)).obj L₁)
      ((Modules.pullback d₂).obj L₂) ((Modules.pullback (z ≫ j₂)).obj L₂) x W hxW
  let V₀ := S.basicOpen r
  have hV : IsAffineOpen V₀ := (isAffineOpen_top S).basicOpen r
  let : IsAffine V₀.toScheme := hV
  let : IsAffine (parameterOpen q ⊤ V₀).toScheme :=
    parameterOpen_affine q ⊤ V₀ (isAffineOpen_top X) hV
  let hmarkTop : ∀ b : Z, (z ≫ q) b ∈ V₀ → z b ∈ (⊤ : X.Opens) := fun _ _ ↦ trivial
  let e := canonicalGraphFrame q ⊤ V₀ z hmarkTop (by
    exact ((Modules.restrictFunctor _).mapIso e₀) ≪≫ Modules.restrictUnitIso _)
  let z₀ := markToParameter q ⊤ V₀ z hmarkTop
  let j₀ := targetInclusion q V₀ π₂ j₂ hq₂
  have hmark : z₀ ≫ j₀ = _ := targetInclusion_mark q V₀ π₂ j₂ hq₂ z
  let : IsClosedImmersion (z₀ ≫ j₀) := by
    rw [hmark]
    infer_instance
  let eZ₂' : (Modules.pullback (z₀ ≫ j₀)).obj (coefficientModule π₂ V₀ L₂) ≅
      SheafOfModules.unit (markOpen q V₀ z).toScheme.ringCatSheaf :=
    (Modules.pullbackCongr hmark).app _ ≪≫
      refinedMarkCoefficientFrame q ⊤ V₀ π₂ j₂ (𝟙 X) hq₂ z hmarkTop
        z (Category.comp_id z) L₂ eZ₂
  refine ⟨r, hxr, hrW, e, ?_⟩
  exact nonempty_pairedSectionData (parameterProjection q ⊤ V₀)
    (compactificationProjection π₁ V₀) (firstInclusion q ⊤ V₀ π₁ j₁ p hq₁)
    (firstMap q ⊤ V₀ p) (firstInclusion_projection q ⊤ V₀ π₁ j₁ p hq₁)
    (compactificationProjection π₂ V₀) j₀
    (targetInclusion_projection q V₀ π₂ j₂ hq₂)
    (secondMap q ⊤ V₀ a) z₀ (closedLift q ⊤ V₀ z hmarkTop p s hs)
    (closedLift_parameter q ⊤ V₀ z hmarkTop p s hs)
    (closedLift_isPullback q ⊤ V₀ z hmarkTop p s hs H) e
    (sourceBaseMap π₁ V₀ d₁)
    (refinedInfinity_disjoint q ⊤ V₀ π₁ j₁ p hq₁ d₁ hd₁)
    (sourceBaseMap π₂ V₀ d₂) (targetInclusion_disjoint q V₀ π₂ j₂ hq₂ d₂ hd₂)
    (puncture_disjoint q ⊤ V₀ z hmarkTop a ha)
    (coefficientModule π₁ V₀ L₁) (coefficientModule_isAmple π₁ V₀ hV L₁ hL₁)
    (coefficientFrame π₁ V₀ d₁ L₁ eD₁)
    (refinedMarkCoefficientFrame q ⊤ V₀ π₁ j₁ p hq₁ z hmarkTop s hs L₁ eZ₁)
    (coefficientModule π₂ V₀ L₂) (coefficientModule_isAmple π₂ V₀ hV L₂ hL₂)
    (coefficientFrame π₂ V₀ d₂ L₂ eD₂) eZ₂'

end Pair

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
