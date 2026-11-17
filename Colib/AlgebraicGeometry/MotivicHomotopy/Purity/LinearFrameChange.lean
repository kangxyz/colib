/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceZero
public import Mathlib.Data.Matrix.Mul

/-!
# Linear changes of marked affine coordinates

The matrix acts on the given coordinates, with inverse the inverse matrix.
It acts compatibly with every parameter restriction and fixes the marked
zero section as a scheme map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped Matrix

universe u

namespace AlgebraicGeometry.AffineSpace

variable {I : Type u} [Fintype I]
  {S T : Scheme.{u}}

/-- The map on the original chart induced by a matrix of global coefficients. -/
def matrixMap (A : Matrix I I Γ(S, ⊤)) : AffineSpace I S ⟶ AffineSpace I S :=
  let p : AffineSpace I S ⟶ S := AffineSpace I S ↘ S
  homOfVector p (A.map p.appTop.hom *ᵥ coord S)

@[reassoc, simp]
theorem matrixMap_over (A : Matrix I I Γ(S, ⊤)) :
    matrixMap A ≫ (AffineSpace I S ↘ S) = AffineSpace I S ↘ S :=
  homOfVector_over _ _

/-- Every entry of the map is the original linear combination of the coordinate sections. -/
theorem matrixMap_appTop_coord (A : Matrix I I Γ(S, ⊤)) (i : I) :
    (matrixMap A).appTop (coord S i) =
      (A.map (AffineSpace I S ↘ S).appTop.hom *ᵥ coord S) i :=
  homOfVector_appTop_coord _ _ _

private theorem matrixMap_appTop_coeff (A : Matrix I I Γ(S, ⊤)) (r : Γ(S, ⊤)) :
    (matrixMap A).appTop ((AffineSpace I S ↘ S).appTop r) =
      (AffineSpace I S ↘ S).appTop r := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, matrixMap_over]

/-- Composition is the contravariant product of the two original coordinate matrices. -/
theorem matrixMap_comp (A B : Matrix I I Γ(S, ⊤)) :
    matrixMap A ≫ matrixMap B = matrixMap (B * A) := by
  let p : AffineSpace I S ⟶ S := AffineSpace I S ↘ S
  apply hom_ext
  · simp only [Category.assoc, matrixMap_over]
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      matrixMap_appTop_coord, RingHom.map_mulVec, matrixMap_appTop_coord]
    have h₁ : (B.map p.appTop.hom).map (matrixMap A).appTop.hom = B.map p.appTop.hom := by
      ext j l
      exact matrixMap_appTop_coeff A (B j l)
    have h₂ : (matrixMap A).appTop ∘ coord S = A.map p.appTop.hom *ᵥ coord S := by
      funext j
      exact matrixMap_appTop_coord A j
    rw [h₁, h₂, Matrix.mulVec_mulVec, Matrix.map_mul]

variable [DecidableEq I]

@[simp]
theorem matrixMap_one : matrixMap (1 : Matrix I I Γ(S, ⊤)) = 𝟙 (AffineSpace I S) := by
  apply hom_ext
  · rw [matrixMap_over, Category.id_comp]
  · intro i
    rw [matrixMap_appTop_coord, Scheme.Hom.id_appTop]
    have h : (1 : Matrix I I Γ(S, ⊤)).map (AffineSpace I S ↘ S).appTop.hom = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [h, Matrix.one_mulVec]
    rfl

/-- An invertible matrix gives an automorphism of the literal affine-space chart. -/
def matrixIso (A : (Matrix I I Γ(S, ⊤))ˣ) : AffineSpace I S ≅ AffineSpace I S where
  hom := matrixMap A.val
  inv := matrixMap A.inv
  hom_inv_id := by rw [matrixMap_comp, A.inv_val, matrixMap_one]
  inv_hom_id := by rw [matrixMap_comp, A.val_inv, matrixMap_one]

omit [DecidableEq I] in
/-- The original zero section is fixed by every linear coordinate map. -/
@[reassoc (attr := simp)]
theorem origin_matrixMap (A : Matrix I I Γ(S, ⊤)) :
    origin S I ≫ matrixMap A = origin S I := by
  let p : AffineSpace I S ⟶ S := AffineSpace I S ↘ S
  apply hom_ext
  · rw [Category.assoc, matrixMap_over]
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, matrixMap_appTop_coord,
      RingHom.map_mulVec, origin_appTop_coord]
    have h : (origin S I).appTop ∘ coord S = 0 := by
      funext j
      exact origin_appTop_coord S I j
    rw [h, Matrix.mulVec_zero]
    rfl

omit [DecidableEq I] in
/-- Restriction of an actual matrix of sections is compatible with the
existing scheme base-change map of affine space. -/
theorem matrixMap_baseChange (f : T ⟶ S) (A : Matrix I I Γ(S, ⊤)) :
    map I f ≫ matrixMap A = matrixMap (A.map f.appTop.hom) ≫ map I f := by
  let pS : AffineSpace I S ⟶ S := AffineSpace I S ↘ S
  let pT : AffineSpace I T ⟶ T := AffineSpace I T ↘ T
  apply hom_ext
  · rw [Category.assoc, matrixMap_over, Category.assoc, map_over, matrixMap_over_assoc]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [matrixMap_appTop_coord, RingHom.map_mulVec, map_appTop_coord, matrixMap_appTop_coord]
    have h₁ : (A.map pS.appTop.hom).map (map I f).appTop.hom =
        (A.map f.appTop.hom).map pT.appTop.hom := by
      ext j l
      change (map I f).appTop (pS.appTop (A j l)) = pT.appTop (f.appTop (A j l))
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, map_over]
    have h₂ : (map I f).appTop ∘ coord S = coord T := by
      funext j
      exact map_appTop_coord f j
    rw [h₁, h₂]

end AlgebraicGeometry.AffineSpace
