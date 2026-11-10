/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.RelativeCohomology.Excision
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Relative Ext excision on the smooth Nisnevich site

The input is a pullback square of actual smooth-site objects, with an open
immersion and an etale morphism that is an isomorphism over the closed
complement. The native geometric descent theorem establishes the section
pullback for every ordinary abelian sheaf. No excision isomorphism or sheaf
gluing conclusion is an input.

The examples use the resulting source-cokernel isomorphism and its restriction
on relative Ext, including detection of zero classes. The final examples
consume Mathlib's functor and natural-transformation laws directly for the
new composite functors, without additional composition or coefficient wrappers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

section GeometricExcision

variable {S : Scheme.{u}} (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

example :
    IsIso ((relativeSourceFunctor.{u + 1} (nisnevichTopology S)).map
      (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)) :=
  isIso_relativeSourceFunctor_map_of_section_descent (nisnevichTopology S) sq
    (fun F ↦ isPullback_op_map_of_iso_complement sq hpb z hcomp F)

variable [HasExt.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]

example (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIso (((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map
      (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄).op) :=
  isIso_relativeCohomologyFunctor_map_of_section_descent (nisnevichTopology S) sq
    (fun G ↦ isPullback_op_map_of_iso_complement sq hpb z hcomp G) F n

example (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).obj
      (op (Arrow.mk sq.f₂₄)))
    (hx : ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map
      (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄).op x = 0) :
    x = 0 := by
  let := isIso_relativeCohomologyFunctor_map_of_section_descent.{w, u + 1}
    (nisnevichTopology S) sq
    (fun G ↦ isPullback_op_map_of_iso_complement sq hpb z hcomp G) F n
  apply (ConcreteCategory.bijective_of_isIso
    (((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map
      (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄).op)).injective
  simpa only [map_zero] using hx

end GeometricExcision

section NativeFunctoriality

variable {S : Scheme.{u}} {j₀ j₁ j₂ : Arrow (SmoothSite S)}
  (f : j₀ ⟶ j₁) (g : j₁ ⟶ j₂)

example :
    (relativeSourceFunctor.{u + 1} (nisnevichTopology S)).map f ≫
        (relativeSourceFunctor.{u + 1} (nisnevichTopology S)).map g =
      (relativeSourceFunctor.{u + 1} (nisnevichTopology S)).map (f ≫ g) :=
  ((relativeSourceFunctor.{u + 1} (nisnevichTopology S)).map_comp f g).symm

variable [HasExt.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]

example (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).obj (op j₂)) :
    ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map f.op
        (((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map g.op x) =
      ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map
        (f ≫ g).op x := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

example {F G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}}
    (η : F ⟶ G) (n : ℕ) :
    ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj F).map f.op ≫
        ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).map η).app (op j₀) =
      ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).map η).app (op j₁) ≫
        ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).obj G).map f.op :=
  ((relativeCohomologyFunctor.{w, u + 1} (nisnevichTopology S) n).map η).naturality f.op

end NativeFunctoriality
