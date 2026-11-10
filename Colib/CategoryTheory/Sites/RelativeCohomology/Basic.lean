/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-!
# Relative Ext of the native representing-sheaf cokernel

For an arrow `j : U ⟶ X` of a site, the relative source is the sheaf cokernel
of `freeYoneda.map j`. A commuting square acts by the native cokernel map.
The construction is the composite of Mathlib's arrow functor and its cokernel
functor, so identity and composition laws are the existing functor laws.

Applying Mathlib's `extFunctor` gives a bifunctor on coefficient sheaves and
opposite site arrows. Its value is `Ext (cokernel (freeYoneda.map j)) F n`.
Restriction in the pair is precomposition by the actual cokernel map, and a
coefficient map acts by postcomposition. The coefficient universe is `max v t`;
the Ext universe `w` is independent of it and of the site object universe `u`.

No monomorphism hypothesis on `j` is needed for these constructions. For a
monomorphism, identifying their long exact sequence requires the short exact
presentation by free representing sheaves. Relative Ext here is not identified
with closed-support cohomology or with cohomology on a small site.

## References

* Adapted from `Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Basic.lean`
  and `Relative/Naturality.lean` at motivic commit
  a6805c4a87cdfd7717dd7a94039246a167f15380.
* The representing sheaf and ordinary cohomology presheaf are the existing
  `Stacks.Cohomology.FreeYonedaUnivLE` constructions.
* The functorial cokernel and Ext bifunctor are used directly from Mathlib.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- The cokernel of the native free representing-sheaf map, functorial in site arrows. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Basic.lean:41-47"
  "adaptation" "The original relative source on native freeYoneda and Mathlib's cokernel functor"]
def relativeSourceFunctor : Arrow C ⥤ Sheaf J AddCommGrpCat.{max v t} :=
  (freeYoneda.{t} J).mapArrow ⋙ coker (Sheaf J AddCommGrpCat.{max v t})

/-- The source assigned to a pair is the actual sheaf cokernel. -/
theorem relativeSourceFunctor_obj (j : Arrow C) :
    (relativeSourceFunctor.{t} J).obj j = cokernel ((freeYoneda.{t} J).map j.hom) := rfl

/-- A commuting square induces the original map of the two free-sheaf cokernels. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Naturality.lean:33-39"
  "adaptation" "The arrow-functor action is the original cokernel.map with its given square"]
theorem relativeSourceFunctor_map {j j' : Arrow C} (f : j ⟶ j') :
    (relativeSourceFunctor.{t} J).map f =
      cokernel.map ((freeYoneda.{t} J).map j.hom) ((freeYoneda.{t} J).map j'.hom)
        ((freeYoneda.{t} J).map f.left) ((freeYoneda.{t} J).map f.right)
        (by rw [← Functor.map_comp, ← Functor.map_comp, ← Arrow.w f]) := rfl

/-- The induced relative-source map commutes with the actual quotient projections. -/
@[simp, reassoc, colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Naturality.lean:41-46"
  "adaptation" "Naturality of the native cokernel projection on the original square"]
theorem relativeSourceFunctor_π_naturality {j j' : Arrow C} (f : j ⟶ j') :
    cokernel.π ((presheafToSheaf J AddCommGrpCat.{max v t}).map
      (Functor.whiskerRight (uliftYoneda.{t}.map j.hom) AddCommGrpCat.free)) ≫
        (relativeSourceFunctor.{t} J).map f =
      (presheafToSheaf J AddCommGrpCat.{max v t}).map
        (Functor.whiskerRight (uliftYoneda.{t}.map f.right) AddCommGrpCat.free) ≫
          cokernel.π ((presheafToSheaf J AddCommGrpCat.{max v t}).map
            (Functor.whiskerRight (uliftYoneda.{t}.map j'.hom) AddCommGrpCat.free)) :=
  cokernel.π_desc _ _ _

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Relative cohomology as the native Ext bifunctor evaluated on relative source cokernels. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Basic.lean:66-68"
  "adaptation" "The original relative Ext groups, packaged with their native functoriality"]
def relativeCohomologyFunctor (n : ℕ) :
    Sheaf J AddCommGrpCat.{max v t} ⥤ (Arrow C)ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  Functor.flip ((relativeSourceFunctor.{t} J).op ⋙ extFunctor n)

/-- The value at a site arrow is Ext from its free-sheaf cokernel. -/
theorem relativeCohomologyFunctor_obj_obj
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (j : Arrow C) :
    ((relativeCohomologyFunctor.{w, t} J n).obj F).obj (op j) =
      AddCommGrpCat.of (Ext.{w} (cokernel ((freeYoneda.{t} J).map j.hom)) F n) := rfl

/-- Relative restriction is precomposition with the original cokernel map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Naturality.lean:63-72"
  "adaptation" "The original relative restriction is the map of the relative Ext functor"]
theorem relativeCohomologyFunctor_obj_map_apply
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) {j j' : Arrow C} (f : j ⟶ j')
    (x : Ext.{w} ((relativeSourceFunctor.{t} J).obj j') F n) :
    ((relativeCohomologyFunctor.{w, t} J n).obj F).map f.op x =
      (Ext.mk₀ ((relativeSourceFunctor.{t} J).map f)).comp x (zero_add n) := rfl

/-- Changing coefficients is the native Ext postcomposition with their degree-zero class. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Naturality.lean:108-115"
  "adaptation" "The original coefficient map is the coefficient action of the Ext bifunctor"]
theorem relativeCohomologyFunctor_map_app_apply
    {F G : Sheaf J AddCommGrpCat.{max v t}} (η : F ⟶ G) (n : ℕ) (j : Arrow C)
    (x : Ext.{w} ((relativeSourceFunctor.{t} J).obj j) F n) :
    ((relativeCohomologyFunctor.{w, t} J n).map η).app (op j) x =
      x.comp (Ext.mk₀ η) (add_zero n) := rfl

end Stacks.Cohomology.FreeYonedaUnivLE
