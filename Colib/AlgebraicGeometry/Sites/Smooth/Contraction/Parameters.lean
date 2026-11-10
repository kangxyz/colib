/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Torus
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Geometric integrality of the native contraction parameters

The existing integral additive model is identified with relative affine space,
and its actual base change supplies the chosen smooth-site affine line.
The existing positive Laurent open and the existing unit section prove that
the chosen multiplicative parameter has nonempty integral geometric fibers.

Adapted from `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/GeometricIntegrality.lean`.
No replacement polynomial or Laurent parameter is installed on the smooth site.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The native integral additive scheme is the relative affine line. -/
def additiveGroupAffineSpaceIso : additiveGroup.{u} ≅
    AffineSpace (ULift.{u} Unit) (Spec (.of (ULift.{u} ℤ))) :=
  Scheme.Spec.mapIso
    (MvPolynomial.uniqueAlgEquiv (ULift.{u} ℤ)
      (ULift.{u} Unit)).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} Unit) (.of (ULift.{u} ℤ))).symm

/-- The comparison preserves the actual native coefficient projection. -/
@[reassoc, simp]
theorem additiveGroupAffineSpaceIso_hom_over :
    additiveGroupAffineSpaceIso.{u}.hom ≫
      (AffineSpace (ULift.{u} Unit) (Spec (.of (ULift.{u} ℤ))) ↘
        Spec (.of (ULift.{u} ℤ))) =
      (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  simp only [additiveGroupAffineSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  change Spec.map _ ≫ Spec.map _ = Spec.map (CommRingCat.ofHom Polynomial.C)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (MvPolynomial.uniqueAlgEquiv (ULift.{u} ℤ) (ULift.{u} Unit)).commutes r

/-- All field-valued fibers of the actual integral additive projection are integral. -/
instance geometricallyIntegral_additiveGroup_projection :
    GeometricallyIntegral (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  have sq : IsPullback additiveGroupAffineSpaceIso.{u}.hom
      (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (AffineSpace (ULift.{u} Unit) (Spec (.of (ULift.{u} ℤ))) ↘
        Spec (.of (ULift.{u} ℤ))) (𝟙 _) :=
    IsPullback.of_horiz_isIso
      ⟨by simp only [additiveGroupAffineSpaceIso_hom_over, Category.comp_id]⟩
  exact MorphismProperty.of_isPullback sq inferInstance

namespace Scheme.SmoothSite

/-- The actual native affine-line parameter inherits geometric integrality by base change. -/
instance additiveGroupObject_geometricallyIntegral (S : Scheme.{u}) :
    GeometricallyIntegral (additiveGroupObject S).hom :=
  inferInstanceAs (GeometricallyIntegral
    (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S)))

/-- The already chosen unit section makes the native multiplicative projection surjective. -/
instance multiplicativeGroupObject_surjective (S : Scheme.{u}) :
    Surjective (multiplicativeGroupObject S).hom := by
  have h : (torusOne S).left ≫ (multiplicativeGroupObject S).hom = 𝟙 S :=
    MorphismProperty.Over.w (torusOne S)
  have : Surjective ((torusOne S).left ≫ (multiplicativeGroupObject S).hom) := by
    rw [h]
    exact ⟨fun x ↦ ⟨x, rfl⟩⟩
  exact Surjective.of_comp (torusOne S).left (multiplicativeGroupObject S).hom

/-- Every field-valued native Laurent fiber is an open subscheme of the affine-line fiber. -/
instance multiplicativeGroupObject_geometricallyReduced (S : Scheme.{u}) :
    GeometricallyReduced (multiplicativeGroupObject S).hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let i : pullback (multiplicativeGroupObject S).hom y ⟶
      pullback (additiveGroupObject S).hom y :=
    pullback.map _ _ _ _ (multiplicativeGroupOpen S).left (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans
        (MorphismProperty.Over.w (multiplicativeGroupOpen S)).symm) (by simp)
  exact isReduced_of_isOpenImmersion i

/-- The actual Laurent open has integral geometric fibers, with no restriction on the base. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/GeometricIntegrality.lean:87-96"
  "adaptation" "The native positive open, actual unit section and native coefficient projection"]
instance multiplicativeGroupObject_geometricallyIntegral (S : Scheme.{u}) :
    GeometricallyIntegral (multiplicativeGroupObject S).hom := by
  have h := MorphismProperty.Over.w (multiplicativeGroupOpen S)
  have : Surjective ((multiplicativeGroupOpen S).left ≫
      (additiveGroupObject S).hom) := by
    rw [h]
    infer_instance
  have : GeometricallyIrreducible (multiplicativeGroupObject S).hom := by
    rw [← h]
    infer_instance
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end Scheme.SmoothSite

end AlgebraicGeometry
