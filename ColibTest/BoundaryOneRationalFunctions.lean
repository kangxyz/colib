/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Functor

open CategoryTheory Polynomial Polynomial.BoundaryOneRationalFunctions

universe u

noncomputable section

namespace BoundaryOneRationalFunctionsTest

/-- The actual localized-unit path, consumed in additive functor notation.
It is only a function, not an additive group homomorphism. -/
def polynomialPath (R : CommRingCat.{u}) (f : functor.obj R) :
    functor.obj (CommRingCat.of R[X]) := Additive.ofMul (homotopy f.toMul)

-- The zero element is fixed as a literal boundary-one rational function.
example (R : CommRingCat.{u}) : polynomialPath R 0 = 0 := by
  change Additive.ofMul (homotopy (1 : group R)) = 0
  rw [homotopy_identity]
  rfl

-- Both endpoint maps are actual polynomial specializations over every commutative ring.
example (R : CommRingCat.{u}) (f : functor.obj R) :
    functor.map (CommRingCat.ofHom (evalRingHom (0 : R))) (polynomialPath R f) = 0 := by
  change Additive (group R) at f
  change Additive.ofMul (map (evalRingHom 0) (homotopy f.toMul)) = 0
  rw [homotopy_zero]
  rfl

example (R : CommRingCat.{u}) (f : functor.obj R) :
    functor.map (CommRingCat.ofHom (evalRingHom (1 : R))) (polynomialPath R f) = f := by
  change Additive (group R) at f
  change Additive.ofMul (map (evalRingHom 1) (homotopy f.toMul)) = f
  rw [homotopy_one]
  rfl

-- This naturality square has no injectivity or nontriviality hypothesis.
example {R S : CommRingCat.{u}} (φ : R ⟶ S) (f : functor.obj R) :
    functor.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.hom)) (polynomialPath R f) =
      polynomialPath S (functor.map φ f) := by
  change Additive (group R) at f
  change Additive.ofMul (map (Polynomial.mapRingHom φ.hom) (homotopy f.toMul)) =
    Additive.ofMul (homotopy (map φ.hom f.toMul))
  rw [homotopy_natural]

-- Literal multiplicative-one faces become zero faces throughout the setwise path.
example {R S : CommRingCat.{u}} (φ : R ⟶ S) (f : group R)
    (hf : functor.map φ (Additive.ofMul f) = 0) :
    functor.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.hom))
      (polynomialPath R (Additive.ofMul f)) = 0 := by
  have hf' : map φ.hom f = 1 := (functor_map_eq_zero_iff φ f).mp hf
  change Additive.ofMul (map (Polynomial.mapRingHom φ.hom) (homotopy f)) = 0
  rw [homotopy_preserves_face_one φ.hom f hf']
  rfl

-- Evaluation at zero on integer polynomials is genuinely noninjective.
example : ¬ Function.Injective (evalRingHom (0 : ℤ)) := by
  intro h
  have hX : (X : ℤ[X]) = 0 := h (by simp)
  exact X_ne_zero hX

-- Instantiate the same path over the actual zero ring, rather than excluding it.
example (f : group PUnit) : map (evalRingHom 1) (homotopy f) = f :=
  homotopy_one f

-- The universe required by the old large-transfer model remains available.
-- No small-transfer replacement is introduced: this is the actual native ULift.
example : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  functor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

example {R S : CommRingCat.{u}} (φ : R ⟶ S) (f : group R) :
    (functor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map φ
      (ULift.up (Additive.ofMul f)) = ULift.up (Additive.ofMul (map φ.hom f)) := rfl

end BoundaryOneRationalFunctionsTest
