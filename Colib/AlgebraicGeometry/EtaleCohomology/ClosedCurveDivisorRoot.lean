/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.ClosedCurveTensorRoot
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget

/-!
# Tensor roots of differences of closed-curve divisors

The chosen module is literally `𝒪(D₊) ⊗ 𝒪(-D₋)`. Its degree is computed from the
entire rings of functions on the two divisors, retaining nonreduced multiplicities.
Equal finite locally free ranks imply degree zero. For actual sections, the native
Cartier theorem and the closed-immersion image factorization supply all divisor data.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D E : X.IdealSheafData)

/-- Full scheme length of a divisor over a field, including its nilpotents. -/
def lengthOver {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    (D : X.IdealSheafData) : ℕ :=
  letI : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom.toAlgebra
  Module.finrank k Γ(D.subscheme, ⊤)

/-- Transport identifies the class of `𝒪(D)` with its native curve-degree class. -/
theorem picardModelAddEquiv_picardClass [IsEffectiveCartierDivisor D] :
    Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace (picardClass D) =
      divisorSchemePicardClass D :=
  Stacks.GluePicard.picardModelAddEquiv_classOf X.toRingedSpace
    (invertibleSheaf' D) (isInvertible_invertibleSheaf_picard D)

/-- Degree of the actual difference module is the difference of full divisor lengths. -/
theorem picardDegree_differenceSheaf {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) [IsCurve k q] [IsProper q]
    (hdim : topologicalKrullDim X ≤ 1)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E] :
    AlgebraicGeometry.picardDegree k q hdim
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
        (X.picardClass (differenceSheaf D E) (isInvertible_differenceSheaf D E))) =
      (lengthOver q D : ℤ) - (lengthOver q E : ℤ) := by
  rw [picardClass_differenceSheaf, map_sub, picardModelAddEquiv_picardClass,
    picardModelAddEquiv_picardClass, map_sub]
  exact congrArg₂ (fun a b : ℤ => a - b)
    (picardDegree_divisorSchemePicardClass k q hdim D)
    (picardDegree_divisorSchemePicardClass k q hdim E)

/-- A finite locally free divisor of rank `d` has full length `d`. -/
theorem lengthOver_eq_rank {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    (D : X.IdealSheafData) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ q) d] :
    lengthOver q D = d :=
  (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank (D.subschemeι ≫ q) d).2

/-- The actual image subscheme of a section over a field is isomorphic to that field. -/
theorem isIso_sectionKernel_structureMap {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X) (hs : s ≫ q = 𝟙 _) :
    IsIso (s.ker.subschemeι ≫ q) := by
  have : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id q s hs
  have h : s.toImage ≫ (s.ker.subschemeι ≫ q) = 𝟙 _ := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs]
  have heq : s.ker.subschemeι ≫ q = inv s.toImage := by
    apply (cancel_epi s.toImage).1
    simpa using h
  rw [heq]
  infer_instance

/-- The image divisor of a section has length one, without a reduced-support replacement. -/
theorem lengthOver_sectionKernel {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X) (hs : s ≫ q = 𝟙 _) :
    lengthOver q s.ker = 1 := by
  have := isIso_sectionKernel_structureMap q s hs
  have : IsIso (s.ker.subschemeι ≫ q).appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map (s.ker.subschemeι ≫ q).op))
  exact finrank_globalSections_divisorSubscheme_eq_one k q s.ker

end Stacks.Divisors

namespace Stacks.Kummer

open Stacks.Divisors

/-- Equal full lengths give an actual tensor root of the specified difference module. -/
@[colib_tag "COL-1210", stacks 03RP
  "Tensor roots of equal-length effective Cartier divisor differences on a smooth proper curve",
  stacks 0AYY "The degree uses the whole divisor scheme, including nonreduced multiplicities"]
theorem exists_schemeTensorPower_iso_differenceSheaf_of_length_eq
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]
    (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (hlen : lengthOver q D = lengthOver q E) {n : ℕ} (hn : IsUnit (n : k)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf D E) := by
  apply exists_schemeTensorPower_iso_of_picardDegree_eq_zero q hn
    (differenceSheaf D E) (isInvertible_differenceSheaf D E)
  rw [picardDegree_differenceSheaf, hlen, sub_self]

/-- Equal finite locally free ranks supply the length hypothesis, including thickened divisors. -/
theorem exists_schemeTensorPower_iso_differenceSheaf_of_rank_eq
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]
    (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ q) d]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (E.subschemeι ≫ q) d]
    {n : ℕ} (hn : IsUnit (n : k)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf D E) :=
  exists_schemeTensorPower_iso_differenceSheaf_of_length_eq q D E
    ((lengthOver_eq_rank q D d).trans (lengthOver_eq_rank q E d).symm) hn

/-- Two actual sections give a tensor root of their kernel-divisor difference.
The native Cartier theorem supplies the Cartier instances;
image factorization supplies degree one. -/
theorem exists_schemeTensorPower_iso_sectionKernel_differenceSheaf
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]
    [SmoothOfRelativeDimension 1 q]
    (s t : Spec (.of k) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    {n : ℕ} (hn : IsUnit (n : k)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker) := by
  have := Stacks.Hilbert.isEffectiveCartierDivisor_ker_section s hs
  have := Stacks.Hilbert.isEffectiveCartierDivisor_ker_section t ht
  exact exists_schemeTensorPower_iso_differenceSheaf_of_length_eq q s.ker t.ker
    ((lengthOver_sectionKernel q s hs).trans (lengthOver_sectionKernel q t ht).symm) hn

end Stacks.Kummer
