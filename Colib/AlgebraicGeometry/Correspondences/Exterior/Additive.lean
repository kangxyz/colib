/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Prime
public import Colib.AlgebraicGeometry.Correspondences.Additive

/-!
# Signed exterior extension on native correspondence cycles

Extend actual native prime exterior images by the original integer coefficients,
using the established native finite-cycle additive extension. No equivalence to
an auxiliary Finsupp model is introduced. This is the signed operation only;
identity and composition laws of a parameter-product functor remain separate.
Adapted from motivic_source_a6805c4, Exterior/Identity/Basic.lean.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

/-- Exterior product with a parameter identity on actual signed native cycles. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean:278-286"
  "adaptation" "Signed extension of actual native exterior image primes"]
def nativeExterior : finiteCorrespondences X.hom Y.hom →+
    finiteCorrespondences (SmoothSite.product X T).hom (SmoothSite.product Y T).hom :=
  liftFiniteCorrespondence X.hom Y.hom (nativeExteriorPrime X Y T)

/-- Original signed multiplicities are retained on each native prime. -/
@[simp↓]
theorem nativeExterior_single (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) (n : ℤ) :
    nativeExterior X Y T (singleFiniteCorrespondence X.hom Y.hom z hz n) =
      n • nativeExteriorPrime X Y T z hz :=
  liftFiniteCorrespondence_single X.hom Y.hom (nativeExteriorPrime X Y T) z hz n

theorem nativeExterior_add (α β : finiteCorrespondences X.hom Y.hom) :
    nativeExterior X Y T (α + β) = nativeExterior X Y T α + nativeExterior X Y T β :=
  map_add _ _ _

theorem nativeExterior_neg (α : finiteCorrespondences X.hom Y.hom) :
    nativeExterior X Y T (-α) = -nativeExterior X Y T α := map_neg _ _

theorem nativeExterior_zsmul (n : ℤ) (α : finiteCorrespondences X.hom Y.hom) :
    nativeExterior X Y T (n • α) = n • nativeExterior X Y T α := map_zsmul _ _ _

attribute [colib_tag "COL-0386", colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean:278-286"
  "adaptation" "Native cycle support, maps and explicitly stated hypotheses"]
  nativeExterior
  nativeExterior_single

attribute [colib_ref "MVW2006" "Lecture 1, Definition 1.9, p. 6"
  "adaptation" "Exterior product with a geometrically integral parameter identity"]
  nativeExterior

end Stacks.Chow
