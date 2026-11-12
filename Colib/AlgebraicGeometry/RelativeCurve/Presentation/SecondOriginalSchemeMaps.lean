/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.WholeZeroLifting
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.CorrectionSquare
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.SecondOriginalOpen

/-!
# Actual scheme maps between the two refined original corrections

The affine and punctured scheme maps come from the inverse original-open
isomorphisms. Their composites into the original polynomial line retain the
specified scalar map on both sides.
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

/-- The first ambient field structure is the literal original structure. -/
@[reassoc] theorem retainedAmbient_original_structure :
    u₁ ≫ (lineSite (k := k) (R := R)).hom = (Q₁).X₄.hom := by
  change ((parameterOpen e.curveProjection U V).ι ≫ e.refinement) ≫
      (lineSite (k := k) (R := R)).hom =
    parameterProjection e.curveProjection U V ≫ V.ι ≫ e.toField
  rw [Category.assoc, e.base_compatibility, parameterProjection_base_assoc]
  all_goals rfl

/-- The inverse puncture comparison keeps the original ambient inclusion. -/
@[reassoc] theorem retainedPunctureIso_inv_original :
    (retainedOriginalPunctureIso e U V D₁).inv ≫ (Q₁).f₂₄.left ≫ u₁ = (O₁ ⊓ D₁).ι := by
  change (retainedOriginalPunctureIso e U V D₁).inv ≫
    pullback.snd (pullback.snd (D₁).ι e.refinement) (parameterOpen e.curveProjection U V).ι ≫
    u₁ = (O₁ ⊓ D₁).ι
  have h := congrArg
    (fun f => (retainedOriginalPunctureIso e U V D₁).inv ≫ f ≫ (O₁).ι)
    (retainedOriginalPunctureIso_hom_left e U V D₁)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι,
    retainedOriginalOpenIso_hom_ι] using h.symm

variable {S : Type u} [CommRing S] [Algebra k S]
  (f : R →ₐ[k] S)

local notation "σ" => secondPolynomialScalar f
local notation "O₂" => secondOriginalOpen p z s x e U V f

local notation "q₂" => coordinateLineProjection S
local notation "π₂" => ZeroNeighborhood.compactProjection S
local notation "v₂" => ZeroNeighborhood.retainedInclusion S O₂

variable (V₂ : (Spec (.of S)).Opens)

local notation "W₂" => parameterOpen q₂ ⊤ V₂
local notation "T₂" => sourceBaseOpen π₂ V₂ v₂

/-- The first-source scheme map uses the inverse first original-open isomorphism. -/
def secondOriginalAmbientScheme : firstSource q₂ ⊤ V₂ (O₂).ι ⟶ (Q₁).X₄.left :=
  pullback.fst (O₂).ι (W₂).ι ≫ (σ ∣_ O₁) ≫ (retainedOriginalOpenIso e U V).inv

/-- The retained-target map uses the inverse first original-puncture isomorphism. -/
def secondOriginalTargetScheme : (T₂).toScheme ⟶ (Q₁).X₂.left :=
  (T₂).ι ≫ secondOriginalPunctureScalar p z s x e U V f ≫
    (retainedOriginalPunctureIso e U V D₁).inv

@[reassoc (attr := simp)] theorem secondOriginalAmbientScheme_original :
    secondOriginalAmbientScheme p z s x e U V f V₂ ≫ u₁ =
      pullback.fst (O₂).ι (W₂).ι ≫ (O₂).ι ≫ σ := by
  simp only [secondOriginalAmbientScheme, Category.assoc,
    retainedOriginalOpenIso_inv_original, morphismRestrict_ι]

/-- The retained second target still maps to the original polynomial puncture. -/
@[reassoc (attr := simp)] theorem secondOriginalTargetScheme_original :
    secondOriginalTargetScheme p z s x e U V f V₂ ≫ (Q₁).f₂₄.left ≫ u₁ =
      (T₂).ι ≫ (punctureOpen S O₂).ι ≫ σ := by
  simp only [secondOriginalTargetScheme, Category.assoc,
    retainedPunctureIso_inv_original, secondOriginalPunctureScalar_original]

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
