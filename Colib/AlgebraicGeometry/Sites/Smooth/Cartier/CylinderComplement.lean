/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.ZeroComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.NativeSections
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison

/-!
# The actual native cylinder zero section and Laurent puncture

The existing native affine section and the existing positive Laurent inclusion
are proved complementary. Both are actual scheme maps on the chosen cylinder.
The final chart comparison discharges its cylinder complement geometrically.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- The fixed native zero point is the actual complement of the fixed native Laurent open. -/
theorem range_native_zero_point (R : CommRingCat.{u}) :
    Set.range (polynomialAffinePoint R 0 ≫ (affineLinePolynomialIso R).inv).left =
      (Set.range (multiplicativeGroupOpen (Spec R)).left)ᶜ := by
  change Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
    (nativePolynomialAffineLineIso R).inv) =
      (Set.range (multiplicativeGroupBaseChangeToAdditive (Spec R)))ᶜ
  rw [polynomial_zero_nativePolynomialAffineLineIso_inv]
  exact range_additiveGroupBaseChangeZero (Spec R)

/-- The full closed complement of the actual cylinder puncture is its existing zero section. -/
theorem range_nativeAffineSection_zero (R : CommRingCat.{u})
    (X : SmoothSite (Spec R)) :
    Set.range (nativeAffineSection R X 0).left =
      (Set.range (openInclusion.app X).left)ᶜ := by
  rw [Scheme.range_fst_of_isPullback (nativeAffineSection_isPullback R X 0)]
  change (productSnd X (additiveGroupObject (Spec R))).left ⁻¹'
      Set.range (polynomialAffinePoint R 0 ≫ (affineLinePolynomialIso R).inv).left =
    (Set.range (productMap (𝟙 X) (multiplicativeGroupOpen (Spec R))).left)ᶜ
  rw [Scheme.range_fst_of_isPullback
      (productMap_right_isPullback X (multiplicativeGroupOpen (Spec R))),
    range_native_zero_point, Set.preimage_compl]

/-- Both full chart fibers determine the actual native Laurent puncture square. -/
theorem exists_native_cartier_puncture_comparison (R : CommRingCat.{u})
    {U Y V D : SmoothSite (Spec R)} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (a : V ⟶ Y) (b : V ⟶ affineLineCylinder.obj D) (d : D ⟶ V)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) (e : D.left ⟶ Z)
    (hpa : IsPullback d.left e a.left i)
    (hpb : IsPullback d.left (𝟙 _) b.left (nativeAffineSection R D 0).left)
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsPullback (etalePullbackFst j a) (etalePullbackSnd j a) j a ∧
      ∃ t : etalePullback j a ⟶ torusCylinder.obj D,
        IsPullback t (etalePullbackSnd j a) (openInclusion.app D) b :=
  exists_open_complement_comparison j a b d i e (nativeAffineSection R D 0)
    (openInclusion.app D) hpa hpb hcomp (range_nativeAffineSection_zero R D)

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
