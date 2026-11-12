/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Cohomology.LocalTriviality
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageAdjunction
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The actual degree-one boundary along a marked base refinement

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/H1ChartVanishing.lean`,
blob `7a0194ccd6de70359095e949bd15f6462ffc9bb6`, specifically its connecting-class
and image-sieve steps, and the colimit argument in
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/LocalEffacement.lean`,
blob `c9fd4621ae67dce2ae3ac82b3063aeaf86970fd0`.

The refinement is an arrow of the original BASE point's category. Only then
is geometric base change applied. A lift on a different neighborhood of the
total space does not meet this statement. The coefficient kernel has its actual
Ext connecting section. An individual image-sieve witness, on the displayed
base refinement, kills that boundary and its original small-site colimit class.

These are lower algebraic steps. They do not assert the existence of the chart
quotient lift, coefficient restriction monicity, a boundary epimorphism, a
big/small cohomology comparison, or strict A¹-invariance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S T : Scheme.{u}} (p : T ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]
  {A : ShortComplex (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})}
  (hA : A.ShortExact)

/-- A class in the literal coefficient kernel has an actual connecting section
on the same geometrically base-changed object. No local vanishing is presumed. -/
theorem markedBase_H1_kernel_has_connecting_section
    (V : Φ.fiber.Elements)
    (x : (cohomologyPresheaf.{u + 1, u + 1} A.X₁ 1).obj
      (op ((baseChange p).obj V.obj)))
    (hx : x.comp (Ext.mk₀ A.f) (add_zero 1) = 0) :
    ∃ y : Ext ((freeYoneda.{u + 1} (nisnevichTopology T)).obj
        ((baseChange p).obj V.obj)) A.X₃ 0,
      y.comp hA.extClass rfl = x :=
  Ext.covariant_sequence_exact₁
    ((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange p).obj V.obj))
    hA x hx rfl

/-- The actual image-sieve witness on a marked BASE refinement kills its
original connecting class. The whole point-fiber marking is kept by `a`. -/
theorem markedBase_H1_boundary_restriction_zero
    {V W : Φ.fiber.Elements} (a : W ⟶ V)
    (y : Ext ((freeYoneda.{u + 1} (nisnevichTopology T)).obj
      ((baseChange p).obj V.obj)) A.X₃ 0)
    (t : A.X₂.obj.obj (op ((baseChange p).obj W.obj)))
    (ht : A.g.hom.app (op ((baseChange p).obj W.obj)) t =
      A.X₃.obj.map ((baseChange p).map a.hom).op
        (extSectionsAddEquiv.{u + 1, u + 1} ((baseChange p).obj V.obj) A.X₃ y)) :
    (cohomologyPresheaf.{u + 1, u + 1} A.X₁ 1).map
      ((baseChange p).map a.hom).op (y.comp hA.extClass rfl) = 0 :=
  boundary_restriction_eq_zero_of_imageSieve (nisnevichTopology T) hA y
    ((baseChange p).map a.hom) ⟨t, ht⟩

/-- The same actual marked-base witness kills the connecting representative in
the unchanged point-neighborhood colimit, before any higher-image comparison. -/
theorem markedBase_H1_boundary_germ_zero
    {V W : Φ.fiber.Elements} (a : W ⟶ V)
    (y : Ext ((freeYoneda.{u + 1} (nisnevichTopology T)).obj
      ((baseChange p).obj V.obj)) A.X₃ 0)
    (t : A.X₂.obj.obj (op ((baseChange p).obj W.obj)))
    (ht : A.g.hom.app (op ((baseChange p).obj W.obj)) t =
      A.X₃.obj.map ((baseChange p).map a.hom).op
        (extSectionsAddEquiv.{u + 1, u + 1} ((baseChange p).obj V.obj) A.X₃ y)) :
    colimit.ι ((Functor.Elements.π Φ.fiber ⋙ baseChange p).op ⋙
      cohomologyPresheaf.{u + 1, u + 1} A.X₁ 1) (op V)
        (y.comp hA.extClass rfl) = 0 := by
  let D := (Functor.Elements.π Φ.fiber ⋙ baseChange p).op ⋙
    cohomologyPresheaf.{u + 1, u + 1} A.X₁ 1
  have hz : D.map a.op (y.comp hA.extClass rfl) = 0 :=
    markedBase_H1_boundary_restriction_zero p Φ hA a y t ht
  have hw := ConcreteCategory.congr_hom (colimit.w D a.op) (y.comp hA.extClass rfl)
  change colimit.ι D (op W) (D.map a.op (y.comp hA.extClass rfl)) =
    colimit.ι D (op V) (y.comp hA.extClass rfl) at hw
  rw [hz, map_zero] at hw
  exact hw.symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
