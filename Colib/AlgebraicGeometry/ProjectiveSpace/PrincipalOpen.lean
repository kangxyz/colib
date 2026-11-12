/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain

/-!
# Principal coordinate opens of native projective space

The actual chart immersion pulls a coordinate open back to the principal open of the original
coordinate ratio. The native `Proj` structure morphism is proper for a finite coordinate set.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial HomogeneousLocalization CategoryTheory

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (k : Type u) [CommRing k] (ι : Type u)

/-- The homogeneous coordinate principal open in the native projective spectrum. -/
def coordinateOpen (i : ι) : (Proj (homogeneousSubmodule ι k)).Opens :=
  Proj.basicOpen (homogeneousSubmodule ι k) (X i)

/-- A projective coordinate open pulls back to the principal open of the literal ratio. -/
theorem coordinateChart_preimage_coordinateOpen (i j : ι) :
    coordinateChart k ι i ⁻¹ᵁ coordinateOpen k ι j =
      PrimeSpectrum.basicOpen (coordinateRatio k ι i j) := by
  simpa [coordinateChart, coordinateOpen, coordinateRatio, Away.isLocalizationElem] using
    Proj.awayι_preimage_basicOpen (homogeneousSubmodule ι k)
      (isHomogeneous_X k i) Nat.one_pos (isHomogeneous_X k j) Nat.one_pos

/-- All homogeneous coordinate opens cover the original projective spectrum. -/
theorem iSup_coordinateOpen_eq_top : (⨆ i, coordinateOpen k ι i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd p hp
  exact Stacks.AlgebraicGeometry.ProjPolyChart.mem_span_X_of_mem_homogeneousSubmodule hd hp

/-- The canonical structure morphism to the original coefficient ring. -/
def toSpec : Proj (homogeneousSubmodule ι k) ⟶ Spec (.of k) :=
  Proj.toSpecZero (homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule ι k 0)))

/-- The coefficient ring is exactly the degree-zero homogeneous piece. -/
theorem coefficientToDegreeZero_bijective :
    Function.Bijective (algebraMap k (homogeneousSubmodule ι k 0)) := by
  constructor
  · intro a b h
    apply MvPolynomial.C_injective (σ := ι)
    simpa only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq] using
      congrArg (fun z : homogeneousSubmodule ι k 0 => (z : MvPolynomial ι k)) h
  · rintro ⟨p, hp⟩
    have hp' : p ∈ (1 : Submodule k (MvPolynomial ι k)) := by
      rwa [← homogeneousSubmodule_zero]
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hp'
    exact ⟨a, Subtype.ext (by rw [SetLike.GradeZero.coe_algebraMap]; exact ha)⟩

instance coefficientToDegreeZero_isIso :
    IsIso (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule ι k 0))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact coefficientToDegreeZero_bijective k ι

/-- The chart projection retains the literal coefficient homomorphism. -/
@[reassoc]
theorem coordinateChart_toSpec (i : ι) :
    coordinateChart k ι i ≫ toSpec k ι =
      Spec.map (CommRingCat.ofHom (coordinateCoefficientHom k ι i)) := by
  rw [toSpec, ← Category.assoc, coordinateChart, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Finite-dimensional native projective space is proper over its coefficient ring. -/
instance isProper_toSpec [Finite ι] : IsProper (toSpec k ι) := by
  have : IsScalarTower k (homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := homogeneousSubmodule ι k 0)
      (A := MvPolynomial ι k) (fun a =>
        (SetLike.GradeZero.coe_algebraMap (homogeneousSubmodule ι k) a).symm)
  have : Algebra.FiniteType (homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (homogeneousSubmodule ι k 0)
      (MvPolynomial ι k)
  unfold toSpec
  infer_instance

end AlgebraicGeometry.ProjectiveSpace
