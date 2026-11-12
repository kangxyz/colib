/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.SecondOriginalSchemeMaps
public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.WholeZeroCylinder

/-! # The second correction restricts the exact first original square

Only comparisons are constructed here. The second owner's actual whole-zero
geometry, base-only pencil, native torus and cylinder remain unchanged. The
coefficient map is arbitrary; no open-immersion or localization premise is
needed for these restriction maps. The first original open and puncture are
transported through their canonical open-image isomorphisms.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
  (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (x : Spec (.of (Polynomial R)))
  (e : OriginalEtalePresentation k (lineSite (k := k) (R := R)).hom p.left
    (polynomialPunctureInclusion (k := k) (R := R)).left z s x)
  (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme] [IsAffine (parameterOpen e.curveProjection U V).toScheme]

local notation "a₁" => polynomialPunctureInclusion (k := k) (R := R)
local notation "Q₁" => retainedCorrectionSquare p a₁ z s x e U V
local notation "u₁" => retainedToOriginal e U V
local notation "O₁" => retainedOriginalOpen e U V
local notation "D₁" => puncture R

local instance : IsAffine (lineSite (k := k) (R := R)).left :=
  inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
local instance : IsAffine ((opensFunctor (lineSite (k := k) (R := R))).obj D₁).left := by
  change IsAffineOpen D₁
  exact IsAffineOpen.Spec_basicOpen _
local instance : IsAffine (O₁).toScheme := retainedOriginalOpen_affine e U V

variable {S : Type u} [CommRing S] [Algebra k S] [Algebra.Smooth k S]
  (f : R →ₐ[k] S)

local notation "σ" => secondPolynomialScalar (k := k) f
local notation "O₂" => secondOriginalOpen (k := k) p z s x e U V f

local notation "q₂" => coordinateLineProjection S
local notation "π₂" => ZeroNeighborhood.compactProjection S
set_option quotPrecheck false in
local notation "j₂" => (O₂).ι ≫ chart S
local notation "hq₂" => inclusion_projection S O₂
local notation "a₂" => Scheme.Opens.ι (puncture S)
local notation "v₂" => ZeroNeighborhood.retainedInclusion S O₂
local notation "φ₂" => overlapToRetained S O₂
local notation "hφ₂" => overlapToRetained_projective S O₂
local notation "b₂" => Spec.map (CommRingCat.ofHom (algebraMap k S))

variable [hOpen : IsAffine (secondOriginalOpen (k := k) p z s x e U V f).toScheme]
  (V₂ : (Spec (.of S)).Opens) [hBase : IsAffine V₂.toScheme]
local instance : IsAffine (punctureOpen S O₂).toScheme := punctureOpen_affine S O₂ hOpen
local instance : IsAffine (puncture S).toScheme := IsAffineOpen.Spec_basicOpen _
local instance : IsAffine (parameterOpen q₂ ⊤ V₂).toScheme := by
  change IsAffineOpen (parameterOpen q₂ ⊤ V₂)
  have h : IsAffineOpen (q₂ ⁻¹ᵁ V₂) := (show IsAffineOpen V₂ from hBase).preimage q₂
  simpa only [parameterOpen, top_inf_eq] using h
local instance : SmoothOfRelativeDimension 1 (v₂ ≫ π₂) := by
  simpa only [ZeroNeighborhood.compactProjection, Category.id_comp] using
    (inferInstance : SmoothOfRelativeDimension 1
      (ZeroNeighborhood.retainedInclusion S O₂ ≫
        (projectiveSpaceOverRing 1 (.of S) ↘ Spec (.of S))))

local notation "W₂" => parameterOpen q₂ ⊤ V₂
local notation "T₂" => sourceBaseOpen π₂ V₂ v₂
set_option quotPrecheck false in
local notation "G₂" => refinedGraph (k := k) b₂ q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂ a₂ v₂ φ₂ hφ₂
set_option quotPrecheck false in
local notation "α₂" => refinedAlpha (k := k) b₂ q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂ a₂

omit [IsAffine Y.left] [Etale p.left] [IsAffine V.toScheme]
  [IsAffine (parameterOpen e.curveProjection U V).toScheme] in
/-- The second first source has its literal original polynomial field structure. -/
private theorem secondFirst_original_structure :
    pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι ≫ (lineSite (k := k) (R := S)).hom =
      (refinedFirstSite (k := k) b₂ q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂).hom := by
  change _ = (firstInclusion q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂ ≫
    compactificationProjection π₂ V₂) ≫ (V₂.ι ≫ b₂)
  simp only [Category.assoc, compactificationProjection, morphismRestrict_ι_assoc,
    firstInclusion_original_assoc, ZeroNeighborhood.compactProjection, Category.id_comp,
    chart_projection_assoc]
  all_goals rfl

omit [IsAffine Y.left] [Etale p.left] [IsAffine V.toScheme]
  [IsAffine (parameterOpen e.curveProjection U V).toScheme] in
/-- The retained second target retains its full base-restricted field structure. -/
private theorem secondTarget_original_structure :
    (T₂).ι ≫ (punctureOpen S O₂).ι ≫ (lineSite (k := k) (R := S)).hom =
      (refinedTargetSite (k := k) b₂ V₂ π₂ v₂).hom := by
  change (T₂).ι ≫ (punctureOpen S O₂).ι ≫ (q₂ ≫ b₂) =
    (sourceBaseMap π₂ V₂ v₂ ≫ compactificationProjection π₂ V₂) ≫ (V₂.ι ≫ b₂)
  rw [sourceBaseMap_projection, morphismRestrict_ι_assoc]
  simp only [Category.assoc,
    ZeroNeighborhood.retainedInclusion, ZeroNeighborhood.compactProjection, Category.id_comp,
    chart_projection_assoc]

/-- The actual second first source maps to the first correction's ambient site. -/
def secondOriginalAmbient : refinedFirstSite (k := k) b₂ q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂ ⟶ (Q₁).X₄ :=
  let m := secondOriginalAmbientScheme (k := k) p z s x e U V f V₂
  SmoothSite.homMk m (by
    let X := lineSite (k := k) (R := R)
    let X₂ := lineSite (k := k) (R := S)
    let ι := pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι
    have hf := MorphismProperty.Over.w (lineMap (k := k) f)
    change σ ≫ X.hom = X₂.hom at hf
    have hm : m ≫ u₁ = ι ≫ σ := by
      exact (secondOriginalAmbientScheme_original (k := k) p z s x e U V f V₂).trans
        (Category.assoc _ _ _).symm
    calc
      _ = m ≫ (u₁ ≫ X.hom) :=
        congrArg (m ≫ ·) (retainedAmbient_original_structure (k := k) p z s x e U V).symm
      _ = (m ≫ u₁) ≫ X.hom := (Category.assoc _ _ _).symm
      _ = (ι ≫ σ) ≫ X.hom := congrArg (· ≫ X.hom) hm
      _ = ι ≫ X₂.hom := (Category.assoc _ _ _).trans (congrArg (ι ≫ ·) hf)
      _ = _ := (Category.assoc _ _ _).trans (secondFirst_original_structure p z s x e U V f V₂))

/-- Original first-puncture sections are restricted along this exact second target map. -/
def secondOriginalTarget : refinedTargetSite (k := k) b₂ V₂ π₂ v₂ ⟶ (Q₁).X₂ :=
  let m := secondOriginalTargetScheme (k := k) p z s x e U V f V₂
  SmoothSite.homMk m (by
    let X := lineSite (k := k) (R := R)
    let X₂ := lineSite (k := k) (R := S)
    let ι := (T₂).ι ≫ (punctureOpen S O₂).ι
    let a := (Q₁).f₂₄
    have hf := MorphismProperty.Over.w (lineMap (k := k) f)
    change σ ≫ X.hom = X₂.hom at hf
    have hA : (Q₁).X₂.hom = a.left ≫ u₁ ≫ X.hom :=
      (MorphismProperty.Over.w a).symm.trans
        (congrArg (a.left ≫ ·) (retainedAmbient_original_structure (k := k) p z s x e U V).symm)
    have hm : m ≫ a.left ≫ u₁ = ι ≫ σ :=
      (secondOriginalTargetScheme_original (k := k) p z s x e U V f V₂).trans
        (Category.assoc _ _ _).symm
    calc
      _ = m ≫ a.left ≫ u₁ ≫ X.hom := congrArg (m ≫ ·) hA
      _ = (m ≫ a.left ≫ u₁) ≫ X.hom := by simp only [Category.assoc]
      _ = (ι ≫ σ) ≫ X.hom := congrArg (· ≫ X.hom) hm
      _ = ι ≫ X₂.hom := (Category.assoc _ _ _).trans (congrArg (ι ≫ ·) hf)
      _ = _ := (Category.assoc _ _ _).trans (secondTarget_original_structure p z s x e U V f V₂))

/-- The second signed restriction now has exactly the first-puncture codomain. -/
def secondOriginalRestriction :
    refinedOverlapSite (k := k) b₂ q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂ a₂ ⟶ (Q₁).X₂ :=
  G₂ ≫ secondOriginalTarget p z s x e U V f V₂

/-- The precise commuting equation used by marked signed composition. -/
@[reassoc] theorem secondOriginalRestriction_ambient :
    secondOriginalRestriction p z s x e U V f V₂ ≫ (Q₁).f₂₄ =
      α₂ ≫ secondOriginalAmbient p z s x e U V f V₂ := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono u₁).mp
  change (refinedTargetMap q₂ ⊤ V₂ π₂ j₂ (O₂).ι hq₂ a₂ v₂ φ₂ hφ₂ ≫
      secondOriginalTargetScheme (k := k) p z s x e U V f V₂) ≫ (Q₁).f₂₄.left ≫ u₁ =
    (pullback.fst (firstMap q₂ ⊤ V₂ (O₂).ι) (secondMap q₂ ⊤ V₂ a₂) ≫
      secondOriginalAmbientScheme (k := k) p z s x e U V f V₂) ≫ u₁
  simp only [Category.assoc, secondOriginalTargetScheme_original,
    secondOriginalAmbientScheme_original, refinedTargetMap_original_assoc,
    overlapToRetained_original_assoc,
    RelativeCurvePencil.RelativeBase.overlapToOriginal_fst_assoc]

/-- The ambient source retains the unchanged original polynomial coefficient map. -/
@[reassoc] theorem secondOriginalAmbient_original :
    (secondOriginalAmbient p z s x e U V f V₂).left ≫ u₁ =
      pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι ≫ σ :=
  secondOriginalAmbientScheme_original p z s x e U V f V₂

/-- The target comparison retains the exact original polynomial puncture. -/
@[reassoc] theorem secondOriginalTarget_original :
    (secondOriginalTarget p z s x e U V f V₂).left ≫ (Q₁).f₂₄.left ≫ u₁ =
      (T₂).ι ≫ (punctureOpen S O₂).ι ≫ σ :=
  secondOriginalTargetScheme_original p z s x e U V f V₂

/-- The target restriction also identifies the original puncture projection,
not just its composite into the ambient polynomial line. -/
@[reassoc] theorem secondOriginalTarget_puncture :
    (secondOriginalTarget p z s x e U V f V₂).left ≫
      (retainedOriginalPunctureIso e U V D₁).hom ≫
        (Spec (.of (Polynomial R))).homOfLE inf_le_right =
    (T₂).ι ≫ secondOriginalPunctureScalar p z s x e U V f ≫
      (Spec (.of (Polynomial R))).homOfLE inf_le_right := by
  change ((T₂).ι ≫ secondOriginalPunctureScalar p z s x e U V f ≫
      (retainedOriginalPunctureIso e U V D₁).inv) ≫
      (retainedOriginalPunctureIso e U V D₁).hom ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The unchanged native cylinder is compatible with the same original scalar map. -/
@[reassoc] theorem secondOriginalCylinder_original :
    (wholeZeroFirstCylinder (k := k) S O₂ V₂).left ≫
      (Contraction.affineLineCylinder.map
        (SmoothSite.openInclusion (affineSite k S) V₂ ≫ affineMorphism f)).left =
    (secondOriginalAmbient p z s x e U V f V₂).left ≫ u₁ ≫
      (lineCylinderIso (k := k) (R := R)).hom.left := by
  rw [Functor.map_comp]
  change (wholeZeroFirstCylinder (k := k) S O₂ V₂).left ≫
      (Contraction.affineLineCylinder.map (SmoothSite.openInclusion (affineSite k S) V₂)).left ≫
      (Contraction.affineLineCylinder.map (affineMorphism f)).left = _
  rw [wholeZeroFirstCylinder_original_assoc]
  have hf := congrArg (fun f => f.left) (lineCylinderIso_naturality f)
  change σ ≫ (lineCylinderIso (k := k) (R := R)).hom.left =
    (lineCylinderIso (k := k) (R := S)).hom.left ≫
      (Contraction.affineLineCylinder.map (affineMorphism f)).left at hf
  have hAmbient := secondOriginalAmbient_original (k := k) p z s x e U V f V₂
  let l := (lineCylinderIso (k := k) (R := R)).hom.left
  calc
    _ = pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι ≫ σ ≫ l :=
      congrArg (fun a => pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι ≫ a) hf.symm
    _ = (pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι ≫ σ) ≫ l := by simp only [Category.assoc]
    _ = _ := (congrArg (· ≫ l) hAmbient.symm).trans (Category.assoc _ _ _)

/-- The entire second zero marking retains the original zero after coefficient extension. -/
@[reassoc] theorem secondOriginalAmbient_zero
    (hzero : Set.range (polynomialZero S) ⊆ O₂) :
    wholeZeroFirstSection (k := k) S O₂ V₂ hzero ≫
      (secondOriginalAmbient p z s x e U V f V₂).left ≫ u₁ =
    V₂.ι ≫ Spec.map (CommRingCat.ofHom f.toRingHom) ≫ polynomialZero R := by
  rw [secondOriginalAmbient_original, wholeZeroFirstSection_original_assoc,
    zeroLift_original_assoc]
  exact congrArg (fun g => V₂.ι ≫ g) (polynomial_zero_scalar_naturality f.toRingHom)

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
