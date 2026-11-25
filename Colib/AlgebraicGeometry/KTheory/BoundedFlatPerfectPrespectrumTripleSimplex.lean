/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNormalizedPullbackAssociativity
public import Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentProduct
public import Colib.AlgebraicGeometry.Scheme.CoefficientLaurentProjection
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-!
# Common simplex for normalized geometric pullback associativity

The actual two routes from total pullback to the three successive pullbacks are
the two triangular faces of the same native tetrahedron. This also gives the
common diagram for the coefficient projection and two actual coefficient arrows.

Adapted from Quillen `BoundedFlat/NormalizedPullbackSimplex.lean:28-118` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The extra binary intermediate
vertices and the joint scalar evaluation are separate from this tetrahedron.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
  CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectTripleSimplex

/-- The original Waldhausen structure on bounded-flat perfect complexes. -/
abbrev structureOn (X : Scheme.{u}) := boundedAboveFlatPerfectWaldhausen X.toRingedSpace

local notation "W" => structureOn
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The chosen-zero normalized pullback along the entire composite. -/
def source : asSmallCategory (W T) ⟶ asSmallCategory (W X) :=
  asSmallCategoryMap (W T) (W X) (NE (f ≫ g ≫ h)) (NZ _)

/-- The intermediate pullback along `g ≫ h` and then along `f`. -/
def left : asSmallCategory (W T) ⟶ asSmallCategory (W X) :=
  asSmallCategoryMap (W T) (W X) ((NE (g ≫ h)).comp (NE f))
    (by simp only [comp_obj, NZ])

/-- The intermediate pullback along `h` and then along `f ≫ g`. -/
def right : asSmallCategory (W T) ⟶ asSmallCategory (W X) :=
  asSmallCategoryMap (W T) (W X) ((NE h).comp (NE (f ≫ g)))
    (by simp only [comp_obj, NZ])

/-- Three successive pullbacks with the original target parenthesization. -/
def target : asSmallCategory (W T) ⟶ asSmallCategory (W X) :=
  asSmallCategoryMap (W T) (W X) ((NE h).comp ((NE g).comp (NE f)))
    (by simp only [comp_obj, NZ])

/-- The original first left edge. -/
def leftFirst : (source f g h).hom.toFunctor ≅ (left f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (NC f (g ≫ h)) AsSmall.up)

/-- The original second left edge, including the functor associator. -/
def leftSecond : (left f g h).hom.toFunctor ≅ (target f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (NC g h) (N f) ≪≫ Functor.associator (N h) (N g) (N f)) AsSmall.up)

/-- The original first right edge, including transport along scheme associativity. -/
def rightFirst : (source f g h).hom.toFunctor ≅ (right f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg N (Category.assoc f g h).symm) ≪≫ NC (f ≫ g) h) AsSmall.up)

/-- The original second right edge, prewhiskered by the pullback along `h`. -/
def rightSecond : (right f g h).hom.toFunctor ≅ (target f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down
    (isoWhiskerRight (isoWhiskerLeft (N h) (NC f g)) AsSmall.up)

/-- The normalized pullback associativity equation survives the small-category construction. -/
theorem two_routes :
    (leftFirst f g h).hom ≫ (leftSecond f g h).hom =
      (rightFirst f g h).hom ≫ (rightSecond f g h).hom := by
  have hcomp := congrArg
    (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (boundedAboveFlatPerfectNormalizedPullbackCompIso_two_routes f g h)
  simpa only [leftFirst, leftSecond, rightFirst, rightSecond, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp,
    Category.assoc] using hcomp

/-- The four literal vertices of the pullback associativity diagram. -/
def vertices : Fin 4 → (asSmallCategory (W T) ⟶ asSmallCategory (W X)) :=
  ![source f g h, left f g h, right f g h, target f g h]

/-- The specified comparisons from total pullback to each vertex. -/
def references : ∀ i, (source f g h).hom.toFunctor ≅ (vertices f g h i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (leftFirst f g h) (Fin.cases (rightFirst f g h)
    (Fin.cases (leftFirst f g h ≪≫ leftSecond f g h) (fun i ↦ Fin.elim0 i))))

/-- The common native tetrahedron of the normalized pullback comparisons. -/
def simplex : ModelSimplex (asSmallCategory (W T)) (asSmallCategory (W X)) 3 :=
  ModelSimplex.ofIsos (source f g h) (vertices f g h) (references f g h)

/-- The first face contains the actual left pullback route. -/
theorem first_face : (simplex f g h).face (SimplexCategory.δ 2) =
    ModelSimplex.triangle (leftFirst f g h).hom (leftSecond f g h).hom
      (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
      (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

/-- The second face contains the actual right route, using the proved associativity equation. -/
theorem second_face : (simplex f g h).face (SimplexCategory.δ 1) =
    ModelSimplex.triangle (rightFirst f g h).hom (rightSecond f g h).hom
      (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
      (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact (two_routes f g h).symm

open Opposite AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent

/-- Specialization to the original pair of coefficient arrows and the coefficient projection. -/
abbrev coefficientSimplex {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b c : Under R} (v : a ⟶ b) (w : b ⟶ c) :=
  simplex (coefficientMap P w) (coefficientMap P v) (projection (op P, a))

/-- The common simplex for the original polynomial coefficient maps and projection. -/
abbrev polynomialCoefficientSimplex {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b c : Under R} (v : a ⟶ b) (w : b ⟶ c) :=
  simplex (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P a)

/-- The common simplex for the original Laurent coefficient maps and projection. -/
abbrev laurentCoefficientSimplex {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b c : Under R} (v : a ⟶ b) (w : b ⟶ c) :=
  simplex (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P a)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectTripleSimplex
