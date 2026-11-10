/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Functor
public import Colib.AlgebraicTopology.SimplicialObject.SetwisePaths
public import Colib.CategoryTheory.CosimplicialObject.Cylinder
public import Colib.RingTheory.AlgebraicSimplex.Basic
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Actual ring-cylinder paths for boundary-one rational functions

The coefficient group is the actual subgroup of localized polynomial units.
Its homotopy is a setwise function, not a group homomorphism. Evaluating its
polynomial parameter in the genuine categorical cylinder gives compatible
paths, which kill homology via the normalized-cycle criterion.

The chain complex is literally Mathlib's `alternatingFaceMapComplex`; its
coefficients, faces and signs are not replaced. All commutative rings are
allowed, including the zero ring and noninjective coefficient maps.

Adapted from `BoundaryOneRationalFunctions/Cylinder.lean` in `kangxyz/motivic`
at a6805c4a87cdfd7717dd7a94039246a167f15380. Generic singular-complex wrappers
are unfolded to the native complexes, and the categorical prism now uses the
existing native ordinal maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u

namespace Polynomial.BoundaryOneRationalFunctions

open _root_.CategoryTheory.CosimplicialObject

/-- The actual coefficient presheaf on the opposite category of commutative rings. -/
def ringPresheaf : CommRingCat.{u}ᵒᵖᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (opOpEquivalence CommRingCat).functor ⋙ functor

variable (Δ : CosimplicialObject CommRingCat.{u}ᵒᵖ)

/-- The genuine categorical cylinder ring. -/
abbrev cylinderRing (n : SimplexCategory) : CommRingCat.{u} :=
  ((Cylinder.obj Δ).obj n).unop

/-- The original simplex ring's injection into the cylinder ring. -/
def cylinderInclusion (n : SimplexCategory) : (Δ.obj n).unop →+* cylinderRing Δ n :=
  (prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj n).unop.hom

/-- Evaluate the polynomial homotopy parameter at the cylinder's interval coordinate. -/
def cylinderEvaluation (t : (Δ.obj ⦋1⦌).unop) (n : SimplexCategory) :
    ((Δ.obj n).unop)[X] →+* cylinderRing Δ n :=
  eval₂RingHom (cylinderInclusion Δ n)
    ((prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj ⦋1⦌).unop.hom t)

theorem cylinderEvaluation_natural (t : (Δ.obj ⦋1⦌).unop)
    {m n : SimplexCategory} (f : m ⟶ n) :
    (((Cylinder.obj Δ).map f).unop.hom).comp (cylinderEvaluation Δ t n) =
      (cylinderEvaluation Δ t m).comp (Polynomial.mapRingHom (Δ.map f).unop.hom) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
    change ((Cylinder.obj Δ).map f).unop.hom (cylinderInclusion Δ n r) =
      cylinderInclusion Δ m ((Δ.map f).unop.hom r)
    have h : (Cylinder.obj Δ).map f ≫
        (prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj n) =
        (prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj m ⟶ Δ.obj m) ≫ Δ.map f := by
      simp [Cylinder.obj]
    exact congrArg (fun a : (Cylinder.obj Δ).obj m ⟶ Δ.obj n => a.unop.hom r) h
  · simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    change ((Cylinder.obj Δ).map f).unop.hom
      ((prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj ⦋1⦌).unop.hom t) =
        (prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj m ⟶ Δ.obj ⦋1⦌).unop.hom t
    have h := prod.map_fst (𝟙 (Δ.obj ⦋1⦌)) (Δ.map f)
    simpa only [Cylinder.obj, Functor.comp_map, Functor.comp_obj, prod.functor_obj_obj,
      prod.functor_obj_map,
      Category.comp_id, unop_comp, CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (fun a => a.unop.hom t) h

/-- A setwise path in the actual singular-cylinder group. -/
def cylinderPath (t : (Δ.obj ⦋1⦌).unop) (n : ℕ)
    (x : ((alternatingFaceMapComplex AddCommGrpCat).obj (Δ.op ⋙ ringPresheaf)).X n) :
    ((alternatingFaceMapComplex AddCommGrpCat).obj ((Cylinder.obj Δ).op ⋙ ringPresheaf)).X n :=
  Additive.ofMul (map (cylinderEvaluation Δ t ⦋n⦌) (homotopy x.toMul))

@[simp] theorem cylinderPath_zero (t : (Δ.obj ⦋1⦌).unop) (n : ℕ) :
    cylinderPath Δ t n 0 = 0 := by
  change Additive.ofMul (map _ (homotopy 1)) = 0
  rw [homotopy_identity, map_one]
  rfl

theorem cylinderPath_face (t : (Δ.obj ⦋1⦌).unop) (n : ℕ)
    (i : Fin (n + 2))
    (x : ((alternatingFaceMapComplex AddCommGrpCat).obj (Δ.op ⋙ ringPresheaf)).X (n + 1)) :
    ringPresheaf.map ((Cylinder.obj Δ).δ i).op (cylinderPath Δ t (n + 1) x) =
      cylinderPath Δ t n (ringPresheaf.map (Δ.δ i).op x) := by
  change Additive.ofMul (map (((Cylinder.obj Δ).δ i).unop.hom)
      (map (cylinderEvaluation Δ t ⦋n + 1⦌) (homotopy x.toMul))) =
    Additive.ofMul (map (cylinderEvaluation Δ t ⦋n⦌)
      (homotopy (map (Δ.δ i).unop.hom x.toMul)))
  rw [← homotopy_natural, ← map_comp, ← map_comp]
  exact congrArg (fun φ => Additive.ofMul (map φ
    (homotopy (Additive.toMul (α := group (Δ.obj ⦋n + 1⦌).unop) x))))
    (cylinderEvaluation_natural Δ t (SimplexCategory.δ i))

theorem cylinderEvaluation_endpoint (t : (Δ.obj ⦋1⦌).unop) (v : Fin 2)
    (n : SimplexCategory) (a : (Δ.obj n).unop)
    (ht : (Δ.map (SimplexCategory.const n ⦋1⦌ v)).unop.hom t = a) :
    (((Cylinder.endpoint Δ v).app n).unop.hom).comp (cylinderEvaluation Δ t n) =
      evalRingHom a := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_C,
      coe_evalRingHom, eval_C]
    change ((Cylinder.endpoint Δ v).app n).unop.hom
      ((prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj n).unop.hom r) = r
    have h := prod.lift_snd (Δ.map (SimplexCategory.const n ⦋1⦌ v)) (𝟙 (Δ.obj n))
    exact congrArg (fun b => b.unop.hom r) h
  · simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_X,
      coe_evalRingHom, eval_X]
    change ((Cylinder.endpoint Δ v).app n).unop.hom
      ((prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj ⦋1⦌).unop.hom t) = a
    have h := prod.lift_fst (Δ.map (SimplexCategory.const n ⦋1⦌ v)) (𝟙 (Δ.obj n))
    exact (congrArg (fun b => b.unop.hom t) h).trans ht

theorem cylinderPath_start (t : (Δ.obj ⦋1⦌).unop)
    (ht : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 0)).unop.hom t = 0)
    (n : ℕ) (x : ((alternatingFaceMapComplex AddCommGrpCat).obj (Δ.op ⋙ ringPresheaf)).X n) :
    ((alternatingFaceMapComplex AddCommGrpCat).map
      (whiskerRight (NatTrans.op (Cylinder.endpoint Δ 0)) ringPresheaf)).f n
        (cylinderPath Δ t n x) = 0 := by
  change Additive.ofMul (map (((Cylinder.endpoint Δ 0).app ⦋n⦌).unop.hom)
    (map (cylinderEvaluation Δ t ⦋n⦌) (homotopy x.toMul))) = 0
  rw [← map_comp, cylinderEvaluation_endpoint Δ t 0 ⦋n⦌ 0 (ht ⦋n⦌), homotopy_zero]
  rfl

theorem cylinderPath_end (t : (Δ.obj ⦋1⦌).unop)
    (ht : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 1)).unop.hom t = 1)
    (n : ℕ) (x : ((alternatingFaceMapComplex AddCommGrpCat).obj (Δ.op ⋙ ringPresheaf)).X n) :
    ((alternatingFaceMapComplex AddCommGrpCat).map
      (whiskerRight (NatTrans.op (Cylinder.endpoint Δ 1)) ringPresheaf)).f n
        (cylinderPath Δ t n x) = x := by
  change Additive.ofMul (map (((Cylinder.endpoint Δ 1).app ⦋n⦌).unop.hom)
    (map (cylinderEvaluation Δ t ⦋n⦌) (homotopy x.toMul))) = x
  rw [← map_comp, cylinderEvaluation_endpoint Δ t 1 ⦋n⦌ 1 (ht ⦋n⦌), homotopy_one]
  rfl

/-- The actual affine rational-function model is acyclic for any ring-valued
cosimplicial interval carrying a coordinate with endpoints zero and one. -/
theorem isZero_homology_of_interval (t : (Δ.obj ⦋1⦌).unop)
    (h0 : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 0)).unop.hom t = 0)
    (h1 : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 1)).unop.hom t = 1)
    (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      (Δ.op ⋙ ringPresheaf)).homology n) :=
  SimplicialObject.isZero_homology_of_setwise_paths
    (Cylinder.simplicialHomotopy Δ ringPresheaf) (cylinderPath Δ t)
    (cylinderPath_zero Δ t) (cylinderPath_face Δ t)
    (cylinderPath_start Δ t h0) (cylinderPath_end Δ t h1) n

variable (R : Type u) [CommRing R]

/-- The concrete algebraic-simplex geometry used for the affine model. -/
abbrev algebraicSimplex : CosimplicialObject CommRingCat.{u}ᵒᵖ :=
  (_root_.AlgebraicSimplex.simplicialRing R).rightOp

theorem algebraicSimplex_interval_zero (n : SimplexCategory) :
    ((algebraicSimplex R).map (SimplexCategory.const n ⦋1⦌ 0)).unop.hom
      (_root_.AlgebraicSimplex.coordinate R 1 1) = 0 := by
  change _root_.AlgebraicSimplex.pullback R
    (SimplexCategory.const n ⦋1⦌ 0).toOrderHom
    (_root_.AlgebraicSimplex.coordinate R 1 1) = 0
  simp [_root_.AlgebraicSimplex.pullback_coordinate, SimplexCategory.const]

@[simp] theorem algebraicSimplex_interval_zero_simp (n : SimplexCategory) :
    ((_root_.AlgebraicSimplex.simplicialRing R).map
      (SimplexCategory.const n ⦋1⦌ 0).op).hom
        (_root_.AlgebraicSimplex.coordinate R 1 1) = 0 :=
  algebraicSimplex_interval_zero R n

theorem algebraicSimplex_interval_one (n : SimplexCategory) :
    ((algebraicSimplex R).map (SimplexCategory.const n ⦋1⦌ 1)).unop.hom
      (_root_.AlgebraicSimplex.coordinate R 1 1) = 1 := by
  change _root_.AlgebraicSimplex.pullback R
    (SimplexCategory.const n ⦋1⦌ 1).toOrderHom
    (_root_.AlgebraicSimplex.coordinate R 1 1) = 1
  simp [_root_.AlgebraicSimplex.pullback_coordinate, SimplexCategory.const]

@[simp] theorem algebraicSimplex_interval_one_simp (n : SimplexCategory) :
    ((_root_.AlgebraicSimplex.simplicialRing R).map
      (SimplexCategory.const n ⦋1⦌ 1).op).hom
        (_root_.AlgebraicSimplex.coordinate R 1 1) = 1 :=
  algebraicSimplex_interval_one R n

/-- In every degree, the actual affine boundary-one rational-function complex
on the actual algebraic simplices has zero homology. This is not yet the
identification with the original correspondence/sheaf kernel. -/
theorem isZero_homology_algebraicSimplex (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((algebraicSimplex R).op ⋙ ringPresheaf)).homology n) :=
  isZero_homology_of_interval (algebraicSimplex R)
    (_root_.AlgebraicSimplex.coordinate R 1 1)
    (algebraicSimplex_interval_zero R) (algebraicSimplex_interval_one R) n

/-- The same acyclicity statement on the literal coordinate-ring simplicial functor. -/
theorem isZero_homology_coordinateRings (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      (_root_.AlgebraicSimplex.simplicialRing R ⋙ functor)).homology n) :=
  isZero_homology_algebraicSimplex R n

end Polynomial.BoundaryOneRationalFunctions

