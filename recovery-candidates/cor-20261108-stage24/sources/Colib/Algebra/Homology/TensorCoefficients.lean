/-
Copyright (c) 2026 Colib contributors and Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Algebra.Homology.MapTotalComplex

/-!
# Coefficients and the signed order of native chain tensor totals

The coefficient functor is the actual functor `- ⊗ M`, applied degreewise. Native
`TotalMap.totalIso` commutes it with the actual total complex; the ordinary module associator
moves the coefficient to the second column. Native `mapBifunctorFlipIso` and the module
braiding switch the two complex factors with the Koszul sign. Neither complex is replaced
by a complex with the same homology, and no coefficient flatness is required.

The small natural-number sign datum is adapted from the private `chainTotalSymmetry`
in StacksFrontier/RingTheory/Koszul/Concatenation/KoszulRegularAppend.lean at
5ed82d14634e8d9576bb844c7bd4e3da66d450e7, lines 470--488. The pinned public symmetry datum
covers cochain complexes indexed by integers only. All totalization, signed-flip, and
coproduct-preservation comparisons remain the native public constructions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace ChainComplex

/-- The natural-chain total signs, exposed as data for the native signed flip. -/
@[instance_reducible] def downNatTotalSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p p' h q
    change p' + 1 = p at h
    subst p
    change (-1 : ℤˣ) ^ ((p' + 1) * q) * 1 = (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ (p' * q)
    rw [add_mul, one_mul, pow_add, mul_one, mul_comm]
  σ_ε₂ := by
    rintro p q q' h
    change q' + 1 = q at h
    subst q
    change (-1 : ℤˣ) ^ (p * (q' + 1)) * (-1 : ℤˣ) ^ p = 1 * (-1 : ℤˣ) ^ (p * q')
    rw [mul_add, mul_one, pow_add, mul_assoc, Int.units_mul_self, mul_one, one_mul]

variable {R : Type u} [CommRing R]

/-- The native signed swap of chain tensor totals, with sign `(-1)^(p*q)` in bidegree `(p,q)`. -/
def tensorOrderIso (K L : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.tensorObj K L ≅ HomologicalComplex.tensorObj L K := by
  letI := downNatTotalSymmetry
  exact HomologicalComplex.mapBifunctorNatIso K L (ComplexShape.down ℕ)
      (BraidedCategory.curriedBraidingNatIso (ModuleCat R)) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)

/-- The ordinary module associator moves the coefficient inside a native tensor bicomplex. -/
def tensorCoefficientsBicomplexIso (M : ModuleCat.{u} R)
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂.TotalMap.mapBicomplex (tensorRight M)
      ((((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L) ≅
    (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj
        (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj L) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p =>
    HomologicalComplex.Hom.isoOfComponents (fun q => α_ (K.X p) (L.X q) M) ?_) ?_
  · intro q q' _
    change (α_ (K.X p) (L.X q) M).hom ≫ K.X p ◁ (L.d q q' ▷ M) =
      ((K.X p ◁ L.d q q') ▷ M) ≫ (α_ (K.X p) (L.X q') M).hom
    simpa only [id_tensorHom, tensorHom_id] using
      (associator_naturality (𝟙 (K.X p)) (L.d q q') (𝟙 M)).symm
  · intro p p' _
    apply HomologicalComplex.hom_ext
    intro q
    change (α_ (K.X p) (L.X q) M).hom ≫ K.d p p' ▷ (L.X q ⊗ M) =
      (K.d p p' ▷ L.X q) ▷ M ≫ (α_ (K.X p') (L.X q) M).hom
    simpa only [tensorHom_id, id_whiskerRight] using
      (associator_naturality (K.d p p') (𝟙 (L.X q)) (𝟙 M)).symm

/-- Tensoring a native total degreewise with `M` is the total with `M` in the second factor. -/
def tensorCoefficientsIso (M : ModuleCat.{u} R) (K L : ChainComplex (ModuleCat.{u} R) ℕ) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (HomologicalComplex.tensorObj K L)) ≅
        HomologicalComplex.tensorObj K
          (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj L) := by
  let D := (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L
  letI : ∀ n : ℕ, PreservesColimitsOfShape
      (Discrete ↥((ComplexShape.down ℕ).π (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⁻¹' {n})) (tensorRight M) :=
    fun _ => preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  exact (HomologicalComplex₂.TotalMap.totalIso
      (c₁₂ := ComplexShape.down ℕ) (tensorRight M) D).symm ≪≫
    HomologicalComplex₂.total.mapIso (tensorCoefficientsBicomplexIso M K L) (ComplexShape.down ℕ)

/-- The signed reverse-order coefficient total uses the same module, maps, and total signs. -/
def tensorCoefficientsReverseIso (M : ModuleCat.{u} R)
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (HomologicalComplex.tensorObj K L)) ≅
        HomologicalComplex.tensorObj L
          (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
  ((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso (tensorOrderIso K L) ≪≫
    tensorCoefficientsIso M L K

end ChainComplex
