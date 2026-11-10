/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# Free representing sheaves on a descent square

If every ordinary abelian sheaf takes a square to a pullback, the native free
representing sheaves form a pushout. The comparison sends a morphism from the
representing sheaf at `X` to its corresponding section over `X`; precomposition
by the representing-sheaf map is restriction along the original site arrow.

The proof uses Mathlib's Yoneda criterion for pushouts and its transport of
pullback squares along equivalences. Stacks supplies both `freeYoneda` and the
section equivalence, including its restriction formula. No sheafification of
set-valued presheaves is assumed, and the coefficient universe `max v t` need
not dominate the object universe of the site.

## References

* The endpoint is adapted from
  `Motivic/Aglib/CategoryTheory/Sites/FreeAbelianSheafPushout.lean:41-70`
  at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380.
* The section representation and its naturality are reused from
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE`.
* For the native Mayer-Vietoris structure with coefficients in the site hom
  universe, use Mathlib's `MayerVietorisSquare.isPushoutAddCommGrpFreeSheaf`
  directly. The present statement only needs abelian-sheaf section descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

set_option backward.isDefEq.respectTransparency false in
/-- Section descent for all ordinary abelian sheaves gives a pushout of the
native free representing sheaves, with their original four structure maps. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/FreeAbelianSheafPushout.lean:41-70"
  "adaptation" "The pushout criterion on native freeYoneda, using the existing section equivalence"]
theorem isPushout_map_freeYoneda (sq : Square C)
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback) :
    (sq.map (freeYoneda.{t} J)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro F
  refine (Square.IsPullback.iff_of_equiv _ _
    (sectionsEquiv sq.X₄ F) (sectionsEquiv sq.X₂ F)
    (sectionsEquiv sq.X₃ F) (sectionsEquiv sq.X₁ F)
    ?_ ?_ ?_ ?_).2 ((h F).map (forget AddCommGrpCat))
  all_goals
    funext g
    exact sectionsEquiv_naturality_left _ F g

end Stacks.Cohomology.FreeYonedaUnivLE
