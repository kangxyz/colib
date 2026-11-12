/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryDiagram
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSections
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Actual retained smooth opens on the component system

The existing diagram construction applies equally to the fixed retained open
and to the fixed full boundary. All maps and vertices below are those actual
objects. Complementarity is transported as a literal equality of ranges.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem retained_range_of_isPullback {P X Y S : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hp : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← hp.isoPullback_hom_fst]
  change Set.range (pullback.fst f g ∘ hp.isoPullback.hom) = _
  rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  {V : Scheme.{u}} (j : V ⟶ U.toScheme) [IsOpenImmersion j]

instance etaleStageOpenRetained_stage_isOpenImmersion (a : Over i) :
    IsOpenImmersion ((etaleStageOpenBoundaryMap X s p i U j).app a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (etaleStageOpenBoundaryMap_isPullback X s p i U j a).flip inferInstance

instance etaleStageOpenRetained_stage_smooth
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (a : Over i) :
    SmoothOfRelativeDimension 1 ((etaleStageOpenBoundaryMap X s p i U j).app a ≫
      (etaleStageOpenStructure X s p i U).app a) :=
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    ((etaleStageOpenBoundaryMap_isPullback X s p i U j a).flip.paste_vert
      (etaleStageOpenStructure_isPullback X s p i U a)) inferInstance

omit [IsOpenImmersion j] in
/-- The entire actual stage boundary is exactly the complement of the actual retained open. -/
theorem etaleStageOpenRetained_stage_complement
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    (hd : Set.range d = (Set.range j)ᶜ) (a : Over i) :
    Set.range ((etaleStageOpenBoundaryMap X s p i U d).app a) =
      (Set.range ((etaleStageOpenBoundaryMap X s p i U j).app a))ᶜ := by
  rw [retained_range_of_isPullback (etaleStageOpenBoundaryMap_isPullback X s p i U d a),
    retained_range_of_isPullback (etaleStageOpenBoundaryMap_isPullback X s p i U j a), hd]
  rfl

omit [IsOpenImmersion j] in
/-- No stage point is omitted from the full retained-open/boundary cover. -/
theorem etaleStageOpenRetained_stage_cover
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    (hd : Set.range d = (Set.range j)ᶜ) (a : Over i)
    (x : (etaleStageOpenDiagram X s p i U).obj a) :
    x ∈ Set.range ((etaleStageOpenBoundaryMap X s p i U j).app a) ∨
      x ∈ Set.range ((etaleStageOpenBoundaryMap X s p i U d).app a) := by
  rw [etaleStageOpenRetained_stage_complement X s p i U j d hd a]
  exact Classical.em _

omit [IsOpenImmersion j] in
/-- The stage cover is genuinely disjoint, not merely a union covering the curve. -/
theorem etaleStageOpenRetained_stage_disjoint
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    (hd : Set.range d = (Set.range j)ᶜ) (a : Over i) :
    Disjoint (Set.range ((etaleStageOpenBoundaryMap X s p i U j).app a))
      (Set.range ((etaleStageOpenBoundaryMap X s p i U d).app a)) := by
  rw [etaleStageOpenRetained_stage_complement X s p i U j d hd a]
  exact disjoint_compl_right

variable (B : BigEtaleSite.{u}) (hX : B.Contains X.left)

instance etaleStageOpenRetained_limit_isOpenImmersion :
    IsOpenImmersion (etaleStageOpenBoundaryLimitMap X s p i U j B hX) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (etaleStageOpenBoundaryLimitMap_isPullback X s p i U j B hX).flip inferInstance

instance etaleStageOpenRetained_limit_smooth
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)] :
    SmoothOfRelativeDimension 1 (etaleStageOpenBoundaryLimitMap X s p i U j B hX ≫
      etaleStageOpenLimitStructure X s p i U B hX) :=
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    ((etaleStageOpenBoundaryLimitMap_isPullback X s p i U j B hX).flip.paste_vert
      (etaleStageOpenLimitStructure_isPullback X s p i U B hX)) inferInstance

omit [IsOpenImmersion j] in
/-- The original complete boundary also remains the exact complement on the limit. -/
theorem etaleStageOpenRetained_limit_complement
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme) (hd : Set.range d = (Set.range j)ᶜ) :
    Set.range (etaleStageOpenBoundaryLimitMap X s p i U d B hX) =
      (Set.range (etaleStageOpenBoundaryLimitMap X s p i U j B hX))ᶜ := by
  rw [retained_range_of_isPullback (etaleStageOpenBoundaryLimitMap_isPullback X s p i U d B hX),
    retained_range_of_isPullback (etaleStageOpenBoundaryLimitMap_isPullback X s p i U j B hX), hd]
  rfl

omit [IsOpenImmersion j] in
theorem etaleStageOpenRetained_limit_cover
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme) (hd : Set.range d = (Set.range j)ᶜ)
    (x : (etaleStageOpenCone X s p i U B hX).pt) :
    x ∈ Set.range (etaleStageOpenBoundaryLimitMap X s p i U j B hX) ∨
      x ∈ Set.range (etaleStageOpenBoundaryLimitMap X s p i U d B hX) := by
  rw [etaleStageOpenRetained_limit_complement X s p i U j B hX d hd]
  exact Classical.em _

omit [IsOpenImmersion j] in
theorem etaleStageOpenRetained_limit_disjoint
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme) (hd : Set.range d = (Set.range j)ᶜ) :
    Disjoint (Set.range (etaleStageOpenBoundaryLimitMap X s p i U j B hX))
      (Set.range (etaleStageOpenBoundaryLimitMap X s p i U d B hX)) := by
  rw [etaleStageOpenRetained_limit_complement X s p i U j B hX d hd]
  exact disjoint_compl_right

/-- An affine fixed retained open gives an affine actual retained limit, hence a
quasi-affine source for the root/auxiliary supplier. -/
instance etaleStageOpenRetained_limit_isAffine [IsAffine V] :
    IsAffine (etaleStageOpenBoundaryCone X s p i U j B hX).pt := by
  have hsource : IsAffine (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).pt :=
    inferInstanceAs (IsAffine (Spec (.of ↥(etaleLocalRing B X.left hX s))))
  have htarget : IsAffine ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i) :=
    inferInstanceAs (IsAffine ((smallEtaleNeighborhoodToSmooth X s).obj i).left)
  have hb : IsAffineHom ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i) :=
    @isAffineHom_of_isAffine _ _ _ hsource htarget
  have hp := (etaleStageOpenBoundaryLimitMap_isPullback X s p i U j B hX).flip.paste_vert
    (etaleStageOpenLimitStructure_isPullback X s p i U B hX)
  have hf : IsAffineHom
      (pullback.snd ((etaleCurveCone X B hX s p).π.app i) (j ≫ U.ι)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip hb
  exact isAffine_of_isAffineHom (pullback.snd ((etaleCurveCone X B hX s p).π.app i) (j ≫ U.ι))

/-- The supplier's quasi-affineness concerns the same literal retained limit vertex. -/
instance etaleStageOpenRetained_limit_isQuasiAffine [IsAffine V] :
    (etaleStageOpenBoundaryCone X s p i U j B hX).pt.IsQuasiAffine := by
  let := etaleStageOpenRetained_limit_isAffine X s p i U j B hX
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
