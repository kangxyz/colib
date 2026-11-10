/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.RelativeCohomology.BoundaryRefinement

/-! # Actual relative Ext sequence consumers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
  {U X : C} (j : U ⟶ X) [Mono j]
  (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)

example : (relativePresentation.{t} J j).ShortExact :=
  relativePresentation_shortExact J j

example : (relativeSequence.{w, t} J j F n).Exact :=
  relativeSequence_exact J j F n

example (x : (cohomologyPresheaf.{w, t} (J := J) F n).obj (op X))
    (hx : (cohomologyPresheaf.{w, t} (J := J) F n).map j.op x = 0) :
    ∃ z : relativeH J j F n, relativeForget J j F n z = x :=
  relative_lift_of_restriction_zero J j F n x hx

example (x : (cohomologyPresheaf.{w, t} (J := J) F n).obj (op U))
    (hx : relativeBoundary J j F n x = 0) :
    ∃ y : (cohomologyPresheaf.{w, t} (J := J) F n).obj (op X),
      (cohomologyPresheaf.{w, t} (J := J) F n).map j.op y = x :=
  restriction_lift_of_relativeBoundary_zero J j F n x hx

example (z : relativeH J j F (n + 1)) (hz : relativeForget J j F (n + 1) z = 0) :
    ∃ x : (cohomologyPresheaf.{w, t} (J := J) F n).obj (op U), relativeBoundary J j F n x = z :=
  relativeBoundary_lift_of_forget_zero J j F n z hz
