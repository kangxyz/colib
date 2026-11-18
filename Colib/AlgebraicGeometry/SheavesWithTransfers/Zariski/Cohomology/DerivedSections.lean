/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import Mathlib.CategoryTheory.Abelian.RightDerived
import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # The derived cohomology presheaf on a site with large objects

The degreewise identification with actual cohomology out of free representables
is natural both in the coefficient sheaf and in the site object. The
coefficient universe dominates the object and morphism universes of the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ModuleSheafCohomology

universe t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => AddCommGrpCat.{max u v t}
local notation "E" => evaluation Cᵒᵖ A
local notation "S" => sheafToPresheaf J A

private theorem evaluation_preservesHomology (U : Cᵒᵖ) :
    ((E).obj U).PreservesHomology :=
  Functor.preservesHomologyOfExact _

variable [HasSheafify J A]

private def evaluationCorepresentation (U : Cᵒᵖ) :
    preadditiveCoyoneda.obj (op ((freeYoneda.{max u t} J).obj U.unop)) ≅ S ⋙ (E).obj U :=
  NatIso.ofComponents (fun F ↦ (sectionsAddEquiv.{max u t} U.unop F).toAddCommGrpIso)
    (fun {F G} f ↦ by
      ext a
      exact sectionsEquiv_naturality.{max u t} U.unop a f)

private theorem evaluationCorepresentation_naturality {U V : Cᵒᵖ} (g : U ⟶ V) :
    preadditiveCoyoneda.map ((freeYoneda.{max u t} J).map g.unop).op ≫
        (evaluationCorepresentation.{t} J V).hom =
      (evaluationCorepresentation.{t} J U).hom ≫ Functor.whiskerLeft S ((E).map g) := by
  ext F a
  exact sectionsEquiv_naturality_left.{max u t} g.unop F a

variable [EnoughInjectives (Sheaf J A)]

private abbrev evaluationDerivedIso (U : Cᵒᵖ) (n : ℕ) :
    (S).rightDerived n ⋙ (E).obj U ≅ (S ⋙ (E).obj U).rightDerived n := by
  letI := evaluation_preservesHomology.{t} (C := C) U
  exact DerivedForget.rightDerivedCompIso S ((E).obj U) n

/-- Naturality of the comparison with right-derived evaluation. The proof is
the evaluation step in `DerivedForget.rightDerivedForgetCohomologyIso_naturality_open`
with abelian presheaves on the given site. -/
private theorem evaluationDerivedIso_naturality (F : Sheaf J A) (n : ℕ)
    {U V : Cᵒᵖ} (g : U ⟶ V) :
    (((S).rightDerived n).obj F).map g ≫ (evaluationDerivedIso.{t} J V n).hom.app F =
      (evaluationDerivedIso.{t} J U n).hom.app F ≫
        (NatTrans.rightDerived (Functor.whiskerLeft S ((E).map g)) n).app F := by
  let := evaluation_preservesHomology.{t} (C := C) U
  let := evaluation_preservesHomology.{t} (C := C) V
  unfold evaluationDerivedIso DerivedForget.rightDerivedCompIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  let K := ((S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions (Sheaf J A)).obj F).as
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_obj]
  unfold HomotopyCategory.homologyFunctor
  change ((E).map g).app (K.sc n).homology ≫ ((K.sc n).mapHomologyIso ((E).obj V)).inv =
    ((K.sc n).mapHomologyIso ((E).obj U)).inv ≫
      ShortComplex.homologyMap ((K.sc n).mapNatTrans ((E).map g))
  rw [NatTrans.app_homology, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem comp_iso_inv_naturality {D : Type*} [Category* D]
    {X Y U V U' V' : D} {f : X ⟶ Y} {a : Y ⟶ V} {b : X ⟶ U} {d : U ⟶ V}
    {r : U' ⟶ V'} (e : U' ≅ U) (j : V' ≅ V)
    (h₁ : f ≫ a = b ≫ d) (h₂ : r ≫ j.hom = e.hom ≫ d) :
    f ≫ (a ≫ j.inv) = (b ≫ e.inv) ≫ r := by
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂, Iso.inv_hom_id_assoc]
  exact h₁

variable [HasExt.{max u v t} (Sheaf J A)]

private def cohomologyIsoRightDerivedSections (U : Cᵒᵖ) (n : ℕ) :
    extFunctorObj ((freeYoneda.{max u t} J).obj U.unop) n ≅ (S ⋙ (E).obj U).rightDerived n :=
  extFunctorObjIsoRightDerived _ _ (evaluationCorepresentation.{t} J U).symm n

/-- The derived functors of forgetting the sheaf condition are the original
free-representable cohomology presheaf functors. -/
@[no_expose]
def cohomologyPresheafFunctorIsoRightDerived (n : ℕ) :
    cohomologyPresheafFunctor.{max u v t, max u t} J n ≅ (S).rightDerived n := by
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun U ↦ ((cohomologyIsoRightDerivedSections.{t} J U n) ≪≫
      (evaluationDerivedIso.{t} J U n).symm).app F) ?_) ?_
  · intro U V g
    have h := extFunctorObjIsoRightDerived_naturality
      ((freeYoneda.{max u t} J).map g.unop) (evaluationCorepresentation.{t} J V).symm
      (evaluationCorepresentation.{t} J U).symm (Functor.whiskerLeft S ((E).map g)) (by
        simp only [Iso.symm_hom]
        rw [Iso.comp_inv_eq, Category.assoc, evaluationCorepresentation_naturality.{t} J g,
          Iso.inv_hom_id_assoc]) n
    have hev := evaluationDerivedIso_naturality.{t} J F n g
    exact comp_iso_inv_naturality
      ((evaluationDerivedIso.{t} J U n).app F) ((evaluationDerivedIso.{t} J V n).app F)
      (NatTrans.congr_app h F) hev
  · intro F G f
    refine NatTrans.ext (funext fun U ↦ ?_)
    exact ((cohomologyIsoRightDerivedSections.{t} J U n) ≪≫
      (evaluationDerivedIso.{t} J U n).symm).hom.naturality f

end Stacks.Cohomology.FreeYonedaUnivLE
