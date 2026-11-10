/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.BoundaryDivisor
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The genuine ordinary weight-one short exact sequence

The divisor identifies the raw norm kernel only on the actual dense integral
affine subsite. Native left exact sheafification, together with the constructed
basis isomorphism, gives its actual sheaf kernel. Surjectivity is likewise local
on genuine covers. No false global presheaf exactness claim is used.

Adapted from Motivic/Cohomology/WeightOne/Geometry/WeightOneExact.lean at
revision a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicSimplex

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne

open _root_.AlgebraicGeometry.Scheme SmoothSite NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- Every genuine local degreewise divisor is injective. -/
theorem localDivisor_injective (n : ℕ)
    (X : (integralAffineProperty k).FullSubcategoryᵒᵖ) :
    Function.Injective ((integralAffineSingularDivisor k n).app X) := by
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  exact affineReducedBoundaryDivisor_injective (product X.unop.obj (smoothSiteObj k n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual local divisor image is the actual raw norm kernel, in every chain degree. -/
theorem localDivisor_exact (n : ℕ)
    (X : (integralAffineProperty k).FullSubcategoryᵒᵖ)
    (z : ((rawReducedSingular k).X n).obj (op X.unop.obj))
    (hz : (rawNorm k n).app (op X.unop.obj) z = 0) :
    ∃ m, (integralAffineSingularDivisor k n).app X m = z := by
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  have hn : affineReducedNorm (product X.unop.obj (smoothSiteObj k n)) z = 0 := by
    change (reducedNorm k).app
      (op (product X.unop.obj (smoothSiteObj k n))) z = 0 at hz
    simpa only [reducedNorm_app] using hz
  exact (affineReducedNorm_eq_zero_iff (product X.unop.obj (smoothSiteObj k n)) z).mp hn

/-- Actual integral-affine divisors present restriction of the original raw kernel. -/
def localKernelIso (n : ℕ) :=
  integralAffineRawKernelIso k (rawNorm k n) (integralAffineSingularDivisor k n)
    (localDivisor_norm k n) (localDivisor_injective k n) (localDivisor_exact k n)

/-- The native sheafified kernel presentation is precisely the specified divisor. -/
theorem sheafifiedKernelDivisor (n : ℕ) :
    integralAffineSheafifyMap k
      ((localKernelIso k n).hom ≫ (integralAffineInclusion k).op.whiskerLeft
        (kernel.ι (rawNorm k n))) = singularSheafDivisor k n :=
  congrArg (integralAffineSheafifyMap k)
    (integralAffineRawKernelIso_hom_ι k (rawNorm k n) (integralAffineSingularDivisor k n)
      (localDivisor_norm k n) (localDivisor_injective k n) (localDivisor_exact k n))

/-- The actual divisor is the genuine kernel of the actual norm in every sheaf degree. -/
def divisorIsKernel (n : ℕ) :
    IsLimit (KernelFork.ofι ((sheafDivisorChainMap k).f n)
      (show (sheafDivisorChainMap k).f n ≫ (reducedNormSheafMap k).f n = 0 from
        singularSheafDivisor_norm k n)) :=
  kernel.isoKernel _ _
    (integralAffineSheafifyKernelIso k (rawNorm k n) (localKernelIso k n))
    ((integralAffineSheafifyKernelIso_hom_ι k (rawNorm k n)
      (localKernelIso k n)).trans (sheafifiedKernelDivisor k n))

/-- Local norm surjectivity gives epimorphisms of actual Nisnevich sheaves in all degrees. -/
theorem norm_epi (n : ℕ) : Epi ((reducedNormSheafMap k).f n) := by
  apply epi_sheafifyMap_of_integral_affine_surjective k (rawNorm k n)
  intro X _ _
  change Function.Surjective ((reducedNorm k).app (op (product X (smoothSiteObj k n))))
  rw [reducedNorm_app]
  exact affineReducedNorm_surjective (product X (smoothSiteObj k n))

/-- The original large boundary-one, reduced-torus and ordinary unit complexes. -/
def shortComplex := ShortComplex.mk (sheafDivisorChainMap k) (reducedNormSheafMap k)
  (sheafDivisorChainMap_norm k)

/-- The genuine weight-one divisor sequence is short exact in every chain degree. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Geometry/WeightOneExact.lean:101-109"
  "adaptation" "Actual ordinary divisor short exactness, all degrees and arbitrary fields"]
theorem shortExact : (shortComplex k).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact {
    exact := ShortComplex.exact_of_f_is_kernel _ (divisorIsKernel k n)
    mono_f := mono_of_isLimit_fork (divisorIsKernel k n)
    epi_g := norm_epi k n }

end AlgebraicGeometry.MotivicCohomology.WeightOne
