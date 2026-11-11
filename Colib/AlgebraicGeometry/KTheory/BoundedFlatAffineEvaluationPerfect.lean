/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients
/-!
# The actual perfect endpoint of affine section evaluation
Evaluation is followed by the existing bounded-flat-to-perfect inclusion. Compactness
of Spec gives stable equivalence of the inclusion, not levelwise equivalence. Coefficient
tracks can always be postcomposed with inclusion. A square using termwise perfect
pullback additionally requires flatness of the scheme morphism.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- Actual lifted section evaluation followed by the unchanged perfect inclusion. -/
def boundedAboveFlatAffinePerfectEvaluationMap (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.obj R ⟶
      originalPrespectrum (perfectComplexesWaldhausen (Spec R).toRingedSpace) :=
  boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
    boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace
/-- Compactness of Spec supplies the stable inclusion comparison, with no levelwise claim. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/BoundedFlatComparison.lean:26-31"
    "ingredient" "Stable inclusion on compact Spec composed with actual affine evaluation"]
theorem boundedAboveFlatAffinePerfectEvaluationMap_isStableEquivalence (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedAboveFlatAffinePerfectEvaluationMap R) :=
  (boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R).comp
    (boundedAboveFlatPerfectSpecPrespectrumMap_isStableEquivalence R)
/-- The all-degree perfect comparison retains evaluation followed by literal inclusion. -/
def boundedAboveFlatAffinePerfectEvaluationKEquiv (R : CommRingCat.{u}) (n : ℕ) :
    (boundedAboveFlatAffineSectionWaldhausen R).K n ≃*
      (perfectComplexesWaldhausen (Spec R).toRingedSpace).K n :=
  (boundedAboveFlatAffineEvaluationKEquiv R n).trans
    (boundedAboveFlatPerfectKEquiv (Spec R).toRingedSpace n)
/-- The exact forward formula, including degree zero. -/
theorem boundedAboveFlatAffinePerfectEvaluationKEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffinePerfectEvaluationKEquiv R n a =
      boundedAboveFlatPerfectToPerfectKMap (Spec R).toRingedSpace n
        (boundedAboveFlatAffineEvaluationKEquiv R n a) := rfl
/-- The original perfect zero-space map is precisely evaluation followed by inclusion. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean:41-50"
    "ingredient" "Original literal inclusion K-equivalence composed with affine \
      evaluation at zero space"]
theorem boundedAboveFlatAffinePerfectEvaluationKEquiv_zeroSpace
    (R : CommRingCat.{u}) (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalZeroSpaceEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) n
        (boundedAboveFlatAffinePerfectEvaluationKEquiv R n a) =
      HomotopyGroup.map ((boundedAboveFlatAffinePerfectEvaluationMap R).map 0)
        ((boundedAboveFlatAffinePerfectEvaluationMap R).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a) := by
  rw [boundedAboveFlatAffinePerfectEvaluationKEquiv_apply,
    boundedAboveFlatPerfectToPerfectPrespectrumMap_zeroSpace_naturality,
    boundedAboveFlatAffineEvaluationKEquiv_zeroSpace]
  exact (HomotopyGroup.map_comp
    ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map 0)
    ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map_point 0)
    ((boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace).map 0)
    ((boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace).map_point 0)
    (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)).symm
/-- The actual stable forward formula retains inclusion, also in connective degree zero. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean:41-50"
    "ingredient" "Original inclusion K-equivalence composed with affine evaluation \
      under the native stable identification"]
theorem boundedAboveFlatAffinePerfectEvaluationKEquiv_stable
    (R : CommRingCat.{u}) (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) n
        (Additive.ofMul (boundedAboveFlatAffinePerfectEvaluationKEquiv R n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedAboveFlatAffinePerfectEvaluationMap R)
        (smallModelKStableEquiv (boundedAboveFlatAffineSectionModel R) n (Additive.ofMul a)) := by
  rw [boundedAboveFlatAffinePerfectEvaluationKEquiv_apply,
    boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality,
    boundedAboveFlatAffineEvaluationKEquiv_stable]
  change _ = (stableHomotopyFunctor (n : ℤ)).map
    (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace) _
  rw [Functor.map_comp]
  rfl
/-- Every coefficient map has a whole comparison ending in the perfect target. -/
def boundedAboveFlatAffinePerfectCoefficientHomotopy {R S : CommRingCat.{u}} (f : R ⟶ S) :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).postcomp
    (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec S).toRingedSpace)
/-- Flatness is required only for the actual termwise-perfect pullback square. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ConeHomotopyComparison.lean:55-66"
    "ingredient" "Actual flat inclusion-pullback comparison pasted with the affine \
      coefficient track"]
def boundedAboveFlatAffinePerfectFlatCoefficientHomotopy
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] :
    Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffinePerfectEvaluationMap S)
      (boundedAboveFlatAffinePerfectEvaluationMap R ≫ perfectFlatPrespectrumMap (Spec.map f)) :=
  ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).postcomp
      (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec S).toRingedSpace)).cast
        (Category.assoc _ _ _) (Category.assoc _ _ _) |>.trans
    ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatPerfectPullbackPrespectrumHomotopy (Spec.map f)).symm).cast
        rfl (Category.assoc _ _ _).symm)
/-- The flat square starts at coefficient restriction followed by perfect evaluation. -/
theorem boundedAboveFlatAffinePerfectFlatCoefficientHomotopy_at_zero
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level n (0, x) =
      (boundedAboveFlatAffinePerfectEvaluationMap S).map n
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x) :=
  (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).at_zero n x
/-- The flat square ends at perfect evaluation followed by actual termwise flat pullback. -/
theorem boundedAboveFlatAffinePerfectFlatCoefficientHomotopy_at_one
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level n (1, x) =
      (perfectFlatPrespectrumMap (Spec.map f)).map n
        ((boundedAboveFlatAffinePerfectEvaluationMap R).map n x) :=
  (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).at_one n x
/-- The flat termwise-perfect square fixes the original zero throughout. -/
theorem boundedAboveFlatAffinePerfectFlatCoefficientHomotopy_at_point
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level n
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec S).toRingedSpace)).point n :=
  (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).at_point n s
/-- The flat square preserves every original structure coordinate independently of track time. -/
theorem boundedAboveFlatAffinePerfectFlatCoefficientHomotopy_comm
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ) (s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level (n + 1)
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec S).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level n (s, x)) t :=
  (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).comm n s x t
/-- Under the necessary flatness hypothesis, the square retains the actual perfect K-map. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ConeHomotopyComparison.lean:55-66"
    "ingredient" "Perfect K-map naturality derived from the actual flat inclusion-pullback track"]
theorem boundedAboveFlatAffinePerfectEvaluationKEquiv_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffinePerfectEvaluationKEquiv S n
        (KMap (boundedAboveFlatAffineSectionsMap_exact f) n a) =
      KMap (perfectFlatPullback_waldhausenExact (Spec.map f)) n
        (boundedAboveFlatAffinePerfectEvaluationKEquiv R n a) := by
  apply (originalZeroSpaceEquiv (perfectComplexesWaldhausen (Spec S).toRingedSpace) n).injective
  rw [boundedAboveFlatAffinePerfectEvaluationKEquiv_zeroSpace,
    boundedAboveFlatAffineSectionZeroSpaceEquiv_naturality,
    exactOriginalZeroSpaceEquiv_naturality, boundedAboveFlatAffinePerfectEvaluationKEquiv_zeroSpace]
  have h := congrFun
    ((boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).homotopyGroupMap_eq 0 n)
    (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)
  exact (HomotopyGroup.map_comp
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map 0)
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map_point 0)
    ((boundedAboveFlatAffinePerfectEvaluationMap S).map 0)
    ((boundedAboveFlatAffinePerfectEvaluationMap S).map_point 0)
    (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)).symm.trans
      (h.trans (HomotopyGroup.map_comp
        ((boundedAboveFlatAffinePerfectEvaluationMap R).map 0)
        ((boundedAboveFlatAffinePerfectEvaluationMap R).map_point 0)
        ((perfectFlatPrespectrumMap (Spec.map f)).map 0)
        ((perfectFlatPrespectrumMap (Spec.map f)).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)))
end AlgebraicGeometry.Scheme.Modules
