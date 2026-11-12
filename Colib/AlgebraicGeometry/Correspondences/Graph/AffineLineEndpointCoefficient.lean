/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.LeftProjectedEndpoint
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
public import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# Actual native affine-line endpoint incidence coefficients

The literal evaluation section is Cartesian over Spec(k[t]). The existing
native additive cylinder is compared to that polynomial coordinate using its
actual isomorphism and the already proved section equation. Both Cartesian
squares are constructed, rather than assumed.

For every graph source component and every genuine finite-correspondence
support, the original finite signed native Tor coefficient is exactly the
length of the full actual incidence local ring. The finite support is flat
only over the one-dimensional parameter, derived from admissibility.
The original source can be disconnected or empty and the field is arbitrary.

This is a local component coefficient statement. The weighted assembly for a
whole finite-flat family, and its equality to the actual endpoint span, remain
separate obligations; they are not asserted here.
Implementation provenance: a new native proof toward motivic
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Graph/Flat/LeftComposition.lean`.
This is not a byte restoration of that source. It does not infer component
flatness over the full source from whole-family flatness. Native geometric and Tor suppliers
are identified by the precise direct imports and SOURCE_REVIEW.md.

-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {k : Type u} [Field k] {X : Scheme.{u}} (b : X ⟶ Spec (.of k)) (a : k)

/-- Evaluation is a section of the literal polynomial-line structure map. -/
@[reassoc (attr := simp)] theorem affineLinePoint_structure :
    Scheme.AffineLineFiber.point a ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 (CommRingCat.of k) := by
    ext r
    exact Polynomial.eval_C
  rw [he, Spec.map_id]

/-- The literal endpoint is the whole Cartesian fiber over evaluation. -/
theorem endpoint_affineLine_isPullback :
    IsPullback (endpoint b a) b
      (pullback.snd b (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
      (Scheme.AffineLineFiber.point a) := by
  have H : IsPullback (endpoint b a ≫ projection b) b b
      (Scheme.AffineLineFiber.point a ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
    rw [endpoint_projection, affineLinePoint_structure]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact H.of_right (endpoint_snd b a) (IsPullback.of_hasPullback b _)

variable (U : SmoothSite (Spec (.of k)))

/-- The existing native additive section is also Cartesian for the actual
polynomial parameter transported along the existing native comparison. -/
theorem nativeSection_affineLine_isPullback :
    IsPullback (SmoothSite.Contraction.nativeAffineSection (.of k) U a).left U.hom
      ((nativeParameterIso (.of k) U).hom ≫
        pullback.snd U.hom
          (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
      (Scheme.AffineLineFiber.point a) := by
  apply (endpoint_affineLine_isPullback U.hom a).of_iso'
    (Iso.refl _) (nativeParameterIso (.of k) U) (Iso.refl _) (Iso.refl _)
  · simpa using (nativeSection_parameterIso (.of k) U a).symm
  · simp
  · simp
  · simp

end AlgebraicGeometry.Scheme.PolynomialSectionPencil

namespace AlgebraicGeometry.Cor

open Stacks.Chow Scheme.PolynomialSectionPencil Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] (U V : Scheme.SmoothSite (Spec (.of k))) (a : k)

local notation "P" => Scheme.SmoothSite.product U (polynomialAffineLine (CommRingCat.of k))
local notation "σ" => polynomialAffineSection (CommRingCat.of k) U a

/-- The actual polynomial section incidence has its full generic local length,
without assuming that a support component is flat over the whole cylinder. -/
theorem polynomialSection_incidenceCoefficient_eq_length
    (s : genericPoints U.left) (w : pullback (C := Scheme) (P).hom V.hom)
    (hw : IsFiniteCorrespondencePoint (P).hom V.hom w)
    (x : genericPoints (correspondenceIncidence U.hom (P).hom V.hom
      (correspondenceGraphMap U.hom (P).hom (σ).left (MorphismProperty.Over.w σ) s.val) w)) :
    correspondenceIncidenceTorCoefficient k U.hom (P).hom V.hom
      (correspondenceGraphMap U.hom (P).hom (σ).left (MorphismProperty.Over.w σ) s.val) w x =
      ((Module.length ((correspondenceIncidence U.hom (P).hom V.hom
        (correspondenceGraphMap U.hom (P).hom (σ).left (MorphismProperty.Over.w σ) s.val)
          w).presheaf.stalk x.val)
        ((correspondenceIncidence U.hom (P).hom V.hom
          (correspondenceGraphMap U.hom (P).hom (σ).left (MorphismProperty.Over.w σ) s.val)
            w).presheaf.stalk x.val)).toNat : ℤ) := by
  let : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    Scheme.SmoothSite.isLocallyNoetherian_overField k U
  let : IsNormal ((𝟭 Scheme).obj U.left) := Scheme.SmoothSite.isNormal_overField k U
  exact correspondenceIncidenceTorCoefficient_eq_length_of_cartesian_endpoint
    U.hom (P).hom V.hom (σ).left (MorphismProperty.Over.w σ)
    (pullback.snd U.hom
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) a
    (endpoint_affineLine_isPullback U.hom a) s w hw x

local notation "N" => affineLineCylinder.obj U
local notation "τ" => nativeAffineSection (CommRingCat.of k) U a

/-- The genuine native additive-cylinder section incidence has the full generic
local length. This applies literally at zero and one and uses the actual
native section, actual finite support, actual incidence and original Tor coefficient. -/
theorem nativeSection_incidenceCoefficient_eq_length
    (s : genericPoints U.left) (w : pullback (C := Scheme) (N).hom V.hom)
    (hw : IsFiniteCorrespondencePoint (N).hom V.hom w)
    (x : genericPoints (correspondenceIncidence U.hom (N).hom V.hom
      (correspondenceGraphMap U.hom (N).hom (τ).left (MorphismProperty.Over.w τ) s.val) w)) :
    correspondenceIncidenceTorCoefficient k U.hom (N).hom V.hom
      (correspondenceGraphMap U.hom (N).hom (τ).left (MorphismProperty.Over.w τ) s.val) w x =
      ((Module.length ((correspondenceIncidence U.hom (N).hom V.hom
        (correspondenceGraphMap U.hom (N).hom (τ).left (MorphismProperty.Over.w τ) s.val)
          w).presheaf.stalk x.val)
        ((correspondenceIncidence U.hom (N).hom V.hom
          (correspondenceGraphMap U.hom (N).hom (τ).left (MorphismProperty.Over.w τ) s.val)
            w).presheaf.stalk x.val)).toNat : ℤ) := by
  let : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    Scheme.SmoothSite.isLocallyNoetherian_overField k U
  let : IsNormal ((𝟭 Scheme).obj U.left) := Scheme.SmoothSite.isNormal_overField k U
  exact correspondenceIncidenceTorCoefficient_eq_length_of_cartesian_endpoint
    U.hom (N).hom V.hom (τ).left (MorphismProperty.Over.w τ)
    ((nativeParameterIso (.of k) U).hom ≫
      pullback.snd U.hom
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) a
    (nativeSection_affineLine_isPullback a U) s w hw x

end AlgebraicGeometry.Cor
