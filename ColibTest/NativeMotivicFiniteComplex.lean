/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.PresheafWithTransfers

universe u
variable (k : Type u) [Field k]

-- Actual objects, with no assumed sheafification instances or restrictions on the field.
example (q n : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicFiniteComplex k q n

example (q n : ℕ) :
    motivicFiniteComplex k q n =
      CochainComplex.mappingCone (n • 𝟙 (motivicComplex k q)) :=
  motivicFiniteComplex_eq k q n

example (q : ℕ) : motivicFiniteComplex k q 0 =
    CochainComplex.mappingCone (0 : motivicComplex k q ⟶ motivicComplex k q) := by
  simp only [motivicFiniteComplex_eq, zero_nsmul]

example (q n : ℕ) :
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (.up ℤ)).obj
      (motivicFiniteComplex k q n) ≅ motivicFiniteSheafComplex k q n :=
  motivicFiniteComplexUnderlyingIso k q n

example (q n : ℕ) (i : ℤ) :
    (motivicFiniteComplex k q n).X i ≅
      (motivicComplex k q).X (i + 1) ⊞ (motivicComplex k q).X i :=
  motivicFiniteComplexXIso k q n i

example (q n : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicFiniteComplex k q n).X i) :=
  isZero_motivicFiniteComplex_X k q n i hi

example (q n : ℕ) (i : ℤ) :
    (motivicFiniteComplex k q n).d i (i + 1) ≫ motivicFiniteComplex.a k q n (i + 1) =
      motivicFiniteComplex.a k q n i ≫ (motivicComplex k q).d i (i + 1) -
        n • motivicFiniteComplex.b k q n i :=
  motivicFiniteComplex.d_a k q n i

example (q n : ℕ) (i : ℤ) :
    (motivicFiniteComplex k q n).d i (i + 1) ≫ motivicFiniteComplex.b k q n (i + 1) =
      -(motivicFiniteComplex.b k q n i ≫ (motivicComplex k q).d (i + 1) (i + 1 + 1)) :=
  motivicFiniteComplex.d_b k q n i

example (q n : ℕ) (i : ℤ) :
    (motivicFiniteComplex.bockstein k q n).f i = motivicFiniteComplex.b k q n i ≫
      ((motivicComplex k q).shiftFunctorObjXIso 1 i (i + 1) rfl).inv :=
  motivicFiniteComplex.bockstein_f k q n i

example (q n m : ℕ) :
    motivicFiniteComplex.insertion k q n m ≫ motivicFiniteComplex.reduction k q n m =
      m • 𝟙 (motivicFiniteComplex k q n) :=
  motivicFiniteComplex.insertion_reduction k q n m

example (q n m : ℕ) :
    motivicFiniteComplex.reduction k q n m ≫ motivicFiniteComplex.insertion k q n m =
      m • 𝟙 (motivicFiniteComplex k q (n * m)) :=
  motivicFiniteComplex.reduction_insertion k q n m

example (q : ℕ) : Homotopy (𝟙 (motivicFiniteComplex k q 1)) 0 :=
  motivicFiniteComplex.contractionOne k q

-- Naturality is checked on the actual transfer-coefficient functor, not an abstract cone.
example (q n : ℕ) {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    CochainComplex.finiteCoefficients.integral ((motivicComplexFunctor k q).obj P) n ≫
        (motivicFiniteComplexFunctor k q n).map f =
      (motivicComplexFunctor k q).map f ≫
        CochainComplex.finiteCoefficients.integral ((motivicComplexFunctor k q).obj Q) n :=
  CochainComplex.finiteCoefficients.integral_naturality n ((motivicComplexFunctor k q).map f)

example (q n m : ℕ) {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    (motivicFiniteComplexFunctor k q (n * m)).map f ≫
        CochainComplex.finiteCoefficients.reduction ((motivicComplexFunctor k q).obj Q) n m =
      CochainComplex.finiteCoefficients.reduction ((motivicComplexFunctor k q).obj P) n m ≫
        (motivicFiniteComplexFunctor k q n).map f :=
  CochainComplex.finiteCoefficients.reduction_naturality
    ((motivicComplexFunctor k q).obj P) n ((motivicComplexFunctor k q).map f) m
