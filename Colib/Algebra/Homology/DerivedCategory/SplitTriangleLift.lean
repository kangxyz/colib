/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Lifting a triangle map through a split inclusion

If its three components factor through the three inclusions, a map
to the original triangle lifts to the triangle of summands. The
same factorizations verify the original three commutative squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [HasShift C ℤ]

/-- Componentwise lifts through monomorphisms give a map of the actual triangles. -/
def liftTriangleMorphism {S T U : Triangle C} (f : S ⟶ U) (i : T ⟶ U)
    [Mono i.hom₁] [Mono i.hom₂] [Mono i.hom₃]
    (a : S.obj₁ ⟶ T.obj₁) (b : S.obj₂ ⟶ T.obj₂) (c : S.obj₃ ⟶ T.obj₃)
    (ha : a ≫ i.hom₁ = f.hom₁) (hb : b ≫ i.hom₂ = f.hom₂)
    (hc : c ≫ i.hom₃ = f.hom₃) : S ⟶ T where
  hom₁ := a
  hom₂ := b
  hom₃ := c
  comm₁ := by
    apply (cancel_mono i.hom₂).1
    calc
      _ = S.mor₁ ≫ f.hom₂ := (Category.assoc _ _ _).trans (congrArg (S.mor₁ ≫ ·) hb)
      _ = f.hom₁ ≫ U.mor₁ := f.comm₁
      _ = _ := (congrArg (· ≫ U.mor₁) ha.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (a ≫ ·) i.comm₁.symm).trans (Category.assoc _ _ _).symm))
  comm₂ := by
    apply (cancel_mono i.hom₃).1
    calc
      _ = S.mor₂ ≫ f.hom₃ := (Category.assoc _ _ _).trans (congrArg (S.mor₂ ≫ ·) hc)
      _ = f.hom₂ ≫ U.mor₂ := f.comm₂
      _ = _ := (congrArg (· ≫ U.mor₂) hb.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (b ≫ ·) i.comm₂.symm).trans (Category.assoc _ _ _).symm))
  comm₃ := by
    let J := shiftFunctor C (1 : ℤ)
    let : Mono (J.map i.hom₁) := inferInstance
    apply (cancel_mono (J.map i.hom₁)).1
    calc
      _ = S.mor₃ ≫ J.map f.hom₁ := (Category.assoc _ _ _).trans
        (congrArg (S.mor₃ ≫ ·) ((J.map_comp _ _).symm.trans (J.congr_map ha)))
      _ = f.hom₃ ≫ U.mor₃ := f.comm₃
      _ = _ := (congrArg (· ≫ U.mor₃) hc.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (c ≫ ·) i.comm₃.symm).trans (Category.assoc _ _ _).symm))

end CategoryTheory.Pretriangulated
