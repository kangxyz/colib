/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-!
# Unbounded hypercohomology on the native free representing sheaf

The source of derived Hom is Stacks' `FreeYonedaUnivLE.freeYoneda`.
Its sheaf, section equivalence, ordinary Ext presheaf, degree-zero comparison,
and both naturality equations are reused directly. No second ordinary-cohomology
construction or compatibility alias is introduced.

For an integer-indexed complex `K`, hypercohomology is the group of morphisms
from this representing sheaf in degree zero to `K[p]` in Mathlib's unbounded
derived category. The coefficient and derived-category universes remain explicit.
No boundedness or enough-injectives hypothesis is imposed.

Stacks' `Cohomology.derivedSectionsPlus` applies to bounded-below complexes.
It does not directly accept the Suslin complexes needed by the motivic consumer,
which are generally unbounded below. The present extension uses the existing
unbounded localization, free representing sheaf and signed shifts. It does not
construct another derived category or a replacement cohomology provider.

## References

* The section-representing object and its ordinary Ext groups are the existing
  Stacks implementation in `DerivedSections.FreeYonedaSectionsUnivLE`.
* Stacks Project, Lemma 18.5.2 (Tag 03AB), for the functorial section representation.
* Stacks Project, Definition 13.27.1 (Tag 06XQ), for Ext as shifted derived Hom.
* Stacks Project, Section 13.11 (Tag 05RR), for unbounded localization and shifts.
* Adapted from `kangxyz/aglib` at `2c34f185fa859e862661f939cd216b07bcccfb26`,
  `Aglib/CategoryTheory/Sites/Hypercohomology/Basic.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- Exactness of evaluation on epimorphisms makes its native representing sheaf projective. -/
@[colib_tag "COL-0304"]
theorem projective_freeYoneda (X : C)
    (hX : ∀ {F G : Sheaf J AddCommGrpCat.{max v t}} (g : F ⟶ G) [Epi g],
      Function.Surjective (g.hom.app (op X))) :
    Projective ((freeYoneda.{t} J).obj X) where
  factors {F G} f g _ := by
    obtain ⟨x, hx⟩ := hX g (sectionsEquiv X G f)
    refine ⟨(sectionsEquiv X F).symm x, (sectionsEquiv X G).injective ?_⟩
    rw [sectionsEquiv_naturality, Equiv.apply_symm_apply, hx]

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Derived Hom from the native free representing sheaves, in every integer degree. -/
@[colib_tag "COL-0304"]
def derivedHomPresheafFunctor (p : ℤ) :
    DerivedCategory (Sheaf J AddCommGrpCat.{max v t}) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  shiftFunctor _ p ⋙ Functor.flip
    ((freeYoneda.{t} J ⋙ DerivedCategory.singleFunctor _ 0).op ⋙ preadditiveCoyoneda)

/-- Unbounded hypercohomology, functorial in actual complexes and site objects. -/
@[colib_tag "COL-0304"]
def hypercohomologyPresheafFunctor (p : ℤ) :
    CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.Q ⋙ derivedHomPresheafFunctor J p

/-- The hypercohomology presheaf of an actual unbounded cochain complex. -/
@[colib_tag "COL-0304"]
abbrev hypercohomologyPresheaf
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (hypercohomologyPresheafFunctor J p).obj K

/-- The value is the actual group of morphisms in the unbounded derived category. -/
theorem hypercohomologyPresheaf_obj
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) (X : C) :
    (hypercohomologyPresheaf J K p).obj (op X) =
      AddCommGrpCat.of
        ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{t} J).obj X) ⟶
          (DerivedCategory.Q.obj K)⟦p⟧) := rfl

/-- Coefficient maps are postcomposition with the shifted localized cochain map. -/
@[colib_tag "COL-0304"]
theorem hypercohomologyPresheafFunctor_map_app_apply
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) (p : ℤ) (X : C) (x : (hypercohomologyPresheaf J K p).obj (op X)) :
    ((hypercohomologyPresheafFunctor J p).map f).app (op X) x =
      x ≫ (DerivedCategory.Q.map f)⟦p⟧' := rfl

/-- Restriction is precomposition by the actual representing-sheaf map. -/
@[colib_tag "COL-0304"]
theorem hypercohomologyPresheaf_map_apply
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (p : ℤ) {X Y : C} (f : X ⟶ Y) (x : (hypercohomologyPresheaf J K p).obj (op Y)) :
    (hypercohomologyPresheaf J K p).map f.op x =
      (DerivedCategory.singleFunctor _ 0).map ((freeYoneda.{t} J).map f) ≫ x := rfl

/-- Actual quasi-isomorphisms induce isomorphisms in every integer degree. -/
@[colib_tag "COL-0304"]
instance hypercohomologyPresheafFunctor_map_isIso
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) [QuasiIso f] (p : ℤ) :
    IsIso ((hypercohomologyPresheafFunctor J p).map f) := by
  change IsIso ((derivedHomPresheafFunctor J p).map (DerivedCategory.Q.map f))
  infer_instance

end Stacks.Cohomology.FreeYonedaUnivLE

attribute [stacks 06XQ
  "derived Hom from the native free representing sheaf in every integer degree"]
  Stacks.Cohomology.FreeYonedaUnivLE.derivedHomPresheafFunctor

attribute [colib_ref "aglib"
  "Aglib/CategoryTheory/Sites/Hypercohomology/Basic.lean"
  "adaptation"
  "Native freeYoneda source, original unbounded derived Hom and maps; no copied source model"]
  Stacks.Cohomology.FreeYonedaUnivLE.projective_freeYoneda
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyPresheafFunctor
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyPresheaf_map_apply
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyPresheafFunctor_map_app_apply
