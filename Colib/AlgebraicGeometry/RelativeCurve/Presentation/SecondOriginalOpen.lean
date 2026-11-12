/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.NativeMarkedMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.RetainedOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.WholeBaseTorus

/-!
# Scalar restriction of the original polynomial open and its puncture

The second open is the full inverse image along the actual polynomial map.
The map between punctures restricts that same scalar map, with its original
polynomial coordinate and without any localization assumption.
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
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))}
  (p : Y ⟶ lineSite (k := k) (R := R))
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (x : Spec (.of (Polynomial R)))
  (e : OriginalEtalePresentation k (lineSite (k := k) (R := R)).hom p.left
    (polynomialPunctureInclusion (k := k) (R := R)).left z s x)
  (U : e.target.Opens) (V : (Spec e.base).Opens)

local notation "O₁" => retainedOriginalOpen e U V
local notation "D₁" => puncture R

variable {S : Type u} [CommRing S] [Algebra k S]
  (f : R →ₐ[k] S)

/-- The literal polynomial coefficient map, with no chosen ambient replacement. -/
abbrev secondPolynomialScalar : Spec (.of (Polynomial S)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom))
/-- The second neighborhood is the full inverse image of the first original open. -/
abbrev secondOriginalOpen : (Spec (.of (Polynomial S))).Opens :=
  secondPolynomialScalar f ⁻¹ᵁ O₁

local notation "σ" => secondPolynomialScalar f
local notation "O₂" => secondOriginalOpen p z s x e U V f
local notation "D₂" => puncture S

omit [Algebra.Smooth k R] in
/-- Polynomial coefficient extension preserves precisely the puncture D(X). -/
theorem secondPolynomialScalar_puncture (y : Spec (.of (Polynomial S)))
    (hy : y ∈ D₂) : σ y ∈ D₁ := by
  change Polynomial.X ∉ y.asIdeal at hy
  change Polynomial.map f.toRingHom Polynomial.X ∉ y.asIdeal
  simpa only [Polynomial.map_X] using hy

/-- The scalar map between the two literal punctured original opens. -/
def secondOriginalPunctureScalar : (punctureOpen S O₂).toScheme ⟶ (O₁ ⊓ D₁).toScheme :=
  IsOpenImmersion.lift (O₁ ⊓ D₁).ι ((punctureOpen S O₂).ι ≫ σ) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ⟨y.property.1, secondPolynomialScalar_puncture f y.val y.property.2⟩)

@[reassoc (attr := simp)] theorem secondOriginalPunctureScalar_original :
    secondOriginalPunctureScalar p z s x e U V f ≫ (O₁ ⊓ D₁).ι =
      (punctureOpen S O₂).ι ≫ σ := IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
