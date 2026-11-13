/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Colib.AlgebraicGeometry.Chow.PrincipalBoundarySupport
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Colib.Util.References

/-!
# Finiteness of the actual polynomial principal-family supports

This applies the genuine boundary-unit construction to the native principal cycle.
Properness, quasi-affineness and the complete boundary prove finiteness over the
unchanged parameter base. The boundary can be nonreduced. Neither flatness of the
support nor a correspondence or endpoint identity is assumed or concluded here.
Integrality and Noetherianness of the actual product are explicit, as in the
componentwise intermediate of the archived `PrincipalFamily.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {R : Type u} [CommRing R] {C S V W B : Scheme.{u}}
  (p : S ⟶ Spec (.of R)) (q : C ⟶ S) [IsAffine S] [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]

set_option backward.isDefEq.respectTransparency.types false in
include j hcover in
/-- Every nonzero coefficient of the literal signed principal family has finite
native integral support over the original affine parameter base. -/
@[colib_tag "COL-1214",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Chow/Vocabulary/PrincipalCycle.lean:208-222"
    "ingredient" "The literal native principal cycle and its order-of-vanishing coefficients"]
theorem principalFamily_support_isFinite (x : parameterSpace (q ≫ p))
    (hx : letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
      Stacks.Chow.principalCycle (parameterSpace (q ≫ p))
        (ambientRationalFunction (q ≫ p) v f) x ≠ 0) :
    IsFinite ((Stacks.Chow.integralComponentAt x).subschemeι ≫ lineMap p q) := by
  have : IsAffineHom (projection p) := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)
  have : IsProper (lineMap p q) :=
    MorphismProperty.of_isPullback (lineMap_isPullback p q).flip inferInstance
  have : IsAffineHom (projection (j ≫ (q ≫ p))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : (parameterSpace (j ≫ (q ≫ p))).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ p)))
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  exact Stacks.Chow.principalCycle_support_isFinite (lineMap p q) (lineMap (q ≫ p) j)
    (ambientUnitOpen (q ≫ p) v f)
    (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
    (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f) x hx

end AlgebraicGeometry.PrincipalFamilyUnitOpen
