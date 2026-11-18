/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Relative
import all Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Relative
import all Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.ChangeOfTopology
import all Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.DerivedSections
import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Relative.Edge.Sections
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Colib.CategoryTheory.Abelian.RightDerived.EdgePostcompose

/-!
# Normalization of the relative change-of-topology comparison

Exact inverse image and the counit agree with the original absolute cohomology
edge after the same evaluation and cohomology identifications. In positive
degree, both maps send a cocycle on the chosen injective resolution to the
same section of the finer resolution. In degree zero, both read the original
sections of the underlying presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ModuleSheafCohomology Stacks.Cohomology

universe t u v

namespace Stacks.Cohomology.FreeYonedaUnivLE

section Topologies

variable {C : Type u} [Category.{v} C] (J K : GrothendieckTopology C)
  [(𝟭 C).IsContinuous J K]

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => AddCommGrpCat.{max u v t}
set_option quotPrecheck false in
local notation "P" => (𝟭 C).sheafPushforwardContinuous A J K
local notation "L" => sheafToPresheaf J A ⋙ presheafToSheaf K A

variable [HasSheafify J A] [HasSheafify K A]

private theorem leftAdjointUniq_comp_homEquiv
    {E D : Type*} [Category* E] [Category* D] {F F' : E ⥤ D} {G : D ⥤ E}
    (a₁ : F ⊣ G) (a₂ : F' ⊣ G) (x : E) (y : D) (f : F'.obj x ⟶ y) :
    a₁.homEquiv x y ((a₁.leftAdjointUniq a₂).hom.app x ≫ f) = a₂.homEquiv x y f := by
  rw [a₁.homEquiv_naturality_right, a₁.homEquiv_leftAdjointUniq_hom_app a₂, a₂.homEquiv_unit]

/-- The free representing sheaf comparison identifies the original sections term by term. -/
private theorem sectionsEquiv_refinementFreeYonedaIso
    (T : C) (F : Sheaf K A) (x : (freeYoneda.{max u t} J).obj T ⟶ ((P).obj F)) :
    sectionsEquiv.{max u t} T F
        ((refinementFreeYonedaIso.{t} J K).inv.app T ≫ (L).map x ≫
          (coarseningAdjunction.{t} J K).counit.app F) =
      sectionsEquiv.{max u t} T ((P).obj F) x := by
  let Q := (uliftYoneda.{max u t} ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj T
  let aJ := sheafificationAdjunction J A
  let aK := sheafificationAdjunction K A
  let α := coarseningAdjunction.{t} J K
  let d := (aJ.comp α).leftAdjointUniq aK
  let f := d.inv.app Q ≫ (L).map x ≫ α.counit.app F
  have h₁ := leftAdjointUniq_comp_homEquiv (aJ.comp α) aK Q F f
  have h₂ : d.hom.app Q ≫ f = (L).map x ≫ α.counit.app F :=
    Iso.hom_inv_id_app_assoc d Q _
  have h₃ : α.homEquiv _ F ((L).map x ≫ α.counit.app F) = x := by
    rw [← α.homEquiv_counit, Equiv.apply_symm_apply]
  have he : aK.homEquiv Q F f = aJ.homEquiv Q ((P).obj F) x :=
    h₁.symm.trans ((congrArg ((aJ.comp α).homEquiv Q F) h₂).trans
      (congrArg (aJ.homEquiv Q ((P).obj F)) h₃))
  exact congrArg (fun p ↦
    uliftYonedaEquiv.{max u t} ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ p)) he

private theorem evaluationEdgePasting {E : Type*} [Category* E]
    {Y Y' V V' X X' : E} (a : X ⟶ Y') (b : Y ≅ Y') (c : V ≅ V')
    (d : V' ⟶ X') (z : Y ⟶ V) (η : Y' ⟶ V')
    (h : z ≫ c.hom = b.hom ≫ η) :
    (a ≫ b.inv) ≫ z ≫ (c.hom ≫ d) = a ≫ η ≫ d := by
  calc
    _ = (a ≫ b.inv) ≫ (z ≫ c.hom) ≫ d := by simp only [Category.assoc]
    _ = (a ≫ b.inv) ≫ (b.hom ≫ η) ≫ d := congrArg (fun x ↦ (a ≫ b.inv) ≫ x ≫ d) h
    _ = _ := by simp

omit [HasSheafify J A] in
/-- The counit for reading finer sheaves in the coarser topology is an isomorphism. -/
theorem isIso_refinementSheafAdjunction_counit_of_le (h : J ≤ K) (F : Sheaf K A) :
    IsIso ((refinementSheafAdjunction.{t} J K).counit.app F) := by
  let Z : Sheaf K A ⥤ Sheaf J A := ObjectProperty.ιOfLE (fun _ hF ↦ hF.of_le h)
  have hZ₁ : Z.Full := by unfold Z; infer_instance
  have hZ₂ : Z.Faithful := by unfold Z; infer_instance
  let : (P).Full := hZ₁
  let : (P).Faithful := hZ₂
  infer_instance

variable [HasExt.{max u v t} (Sheaf J A)] [HasExt.{max u v t} (Sheaf K A)]
  [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf K A)]

/-- Evaluation of the prescribed cohomology edge is the edge for sections over the object. -/
private theorem cohomologyPresheafChangeOfTopology_app_eq_sectionsEdge
    (F : Sheaf K A) (U : Cᵒᵖ) (n : ℕ)
    [((𝟭 C).sheafPushforwardContinuous A J K).PreservesInjectiveObjects] :
    ((cohomologyPresheafChangeOfTopology.{t} J K n).app F).app U =
      (cohomologyIsoRightDerivedSections.{t} J U n).hom.app ((P).obj F) ≫
        (RightDerivedEdge.edge P (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj U) n).app F ≫
        (cohomologyIsoRightDerivedSections.{t} K U n).inv.app F := by
  let E := (evaluation Cᵒᵖ A).obj U
  let : E.PreservesHomology := evaluation_preservesHomology.{t} (C := C) U
  let η := (RightDerivedEdge.edge P (sheafToPresheaf J A ⋙ E) n).app F
  let edge := RightDerivedEdge.edge P (sheafToPresheaf J A) n
  let a := (cohomologyIsoRightDerivedSections.{t} J U n).hom.app ((P).obj F)
  let b := (evaluationDerivedIso.{t} J U n).app ((P).obj F)
  let c := (evaluationDerivedIso.{t} K U n).app F
  let d := (cohomologyIsoRightDerivedSections.{t} K U n).inv.app F
  have h := RightDerivedEdge.map_edge_comp_exactPostcomposition
    P (sheafToPresheaf J A) E n F
  rw [← derivedForgetCompIso_hom_app_eq_moduleComparison
        (P ⋙ sheafToPresheaf J A) E F n,
    ← derivedForgetCompIso_hom_app_eq_moduleComparison
        (sheafToPresheaf J A) E ((P).obj F) n] at h
  change (a ≫ b.inv) ≫ (edge.app F).app U ≫ (c.hom ≫ d) = a ≫ η ≫ d
  exact evaluationEdgePasting a b c d ((edge.app F).app U) η h

private theorem cancel_inverse_postcomposition {E : Type*} [Category* E]
    {W X Y Z : E} (a : W ⟶ X) (b : X ⟶ Y) (c : Z ≅ Y) (d : W ⟶ Z)
    (h : a ≫ b = d ≫ c.hom) : a ≫ b ≫ c.inv = d := by
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

section Refinement

variable [(sheafToPresheaf J A ⋙ presheafToSheaf K A).Additive]
  [PreservesFiniteLimits (sheafToPresheaf J A ⋙ presheafToSheaf K A)]
  [PreservesFiniteColimits (sheafToPresheaf J A ⋙ presheafToSheaf K A)]

private theorem cohomologyPresheafChangeOfTopology_app_eq_refinement
    (F : Sheaf K A) (U : Cᵒᵖ) (n : ℕ)
    (hε : IsIso ((coarseningAdjunction.{t} J K).counit.app F)) :
    ((cohomologyPresheafChangeOfTopology.{t} J K n).app F).app U =
      refinementCohomologyComparisonAt.{max u v t, max u t} J K
        (refinementFreeYonedaIso.{t} J K) (coarseningAdjunction.{t} J K) F n U.unop := by
  let := coarsening_preservesInjectiveObjects.{t} J K
  let := coarsening_preservesFiniteLimits.{t} J K
  let := hε
  let Q := sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj U
  let W := (freeYoneda.{max u t} J).obj U.unop
  let W' := (freeYoneda.{max u t} K).obj U.unop
  let a := (evaluationCorepresentation.{t} J U).symm
  let b := (evaluationCorepresentation.{t} K U).symm
  let adj := coarseningAdjunction.{t} J K
  let i := (refinementFreeYonedaIso.{t} J K).app U.unop
  have hSections : ∀ (G : Sheaf K A) (s : W ⟶ (P).obj G),
      b.inv.app G (i.inv ≫ (L).map s ≫ adj.counit.app G) = a.inv.app ((P).obj G) s := by
    intro G s
    exact sectionsEquiv_refinementFreeYonedaIso.{t} J K U.unop G s
  have h := sectionsEdge_eq_refinement adj Q W W' a b i F n hSections
  refine (cohomologyPresheafChangeOfTopology_app_eq_sectionsEdge.{t} J K F U n).trans ?_
  exact cancel_inverse_postcomposition _ _
    ((cohomologyIsoRightDerivedSections.{t} K U n).app F) _ h

end Refinement

/-- The original cohomology edge, evaluated at an object, is the exact-refinement map. -/
theorem cohomologyChangeOfTopologyAt_eq_refinement (F : Sheaf K A) (U : C) (n : ℕ)
    (hε : IsIso ((refinementSheafAdjunction.{t} J K).counit.app F)) :
    ((cohomologyPresheafChangeOfTopology.{t} J K n).app F).app (op U) =
      cohomologyChangeOfTopologyViaRefinementAt.{t} J K F n U := by
  let := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  let : (L).Additive := Functor.additive_of_preserves_binary_products _
  exact cohomologyPresheafChangeOfTopology_app_eq_refinement.{t} J K F (op U) n hε

/-- The original sections edge fits the signed localization square. -/
theorem relativeCohomologyChangeOfTopology_boundary_edge {U X : C} (j : U ⟶ X)
    [Mono j] (F : Sheaf K A) (n : ℕ)
    (hε : IsIso ((refinementSheafAdjunction.{t} J K).counit.app F)) :
    relativeBoundary.{max u v t, max u t} J j ((P).obj F) n ≫
        relativeCohomologyChangeOfTopology.{t} J K j F (n + 1) =
      ((cohomologyPresheafChangeOfTopology.{t} J K n).app F).app (op U) ≫
        relativeBoundary.{max u v t, max u t} K j F n :=
  (relativeCohomologyChangeOfTopology_boundary.{t} J K j F n).trans
    (congrArg (· ≫ relativeBoundary.{max u v t, max u t} K j F n)
      (cohomologyChangeOfTopologyAt_eq_refinement.{t} J K F U n hε).symm)

end Topologies

end Stacks.Cohomology.FreeYonedaUnivLE

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

variable (k : Type u) [Field k]

local notation "B" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.zariskiTopology B
local notation "K" => SmoothSite.nisnevichTopology B
set_option hygiene false in
set_option quotPrecheck false in
local notation "P" => SmoothSite.nisnevichToZariskiSheaf B AddCommGrpCat.{u + 1}

/-- The canonical absolute comparison at each smooth scheme is the exact-refinement map
used in the relative localization sequence. -/
theorem zariskiCohomologyComparison_app_eq_refinement (F : SheafWithTransfers.{u + 1} k)
    (n : ℕ) (X : SmoothSite B) :
    let comparison := (zariskiCohomologyComparison k F n).app (op X)
    let refinement := zariskiRefinementCohomologyComparisonAt k F n X
    comparison = refinement :=
  cohomologyChangeOfTopologyAt_eq_refinement.{u + 1} J K ((toSheaf k).obj F) X n
    (isIso_refinementSheafAdjunction_counit_of_le.{u + 1}
      J K (SmoothSite.zariskiTopology_le_nisnevichTopology B) ((toSheaf k).obj F))

/-- The earlier canonical absolute map fits the original signed localization square. -/
@[colib_tag "COL-1308"]
theorem zariskiRelativeCohomologyComparison_boundary_edge {U X : SmoothSite B} (j : U ⟶ X)
    [Mono j] (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    let FNis := (toSheaf k).obj F
    let FZar := (P).obj FNis
    let boundaryZar := relativeBoundary.{u + 1, u + 1} J j FZar n
    let boundaryNis := relativeBoundary.{u + 1, u + 1} K j FNis n
    let compareAt := (zariskiCohomologyComparison k F n).app (op U)
    let compareRelative := zariskiRelativeCohomologyComparison k j F (n + 1)
    boundaryZar ≫ compareRelative = compareAt ≫ boundaryNis :=
  relativeCohomologyChangeOfTopology_boundary_edge.{u + 1} (C := SmoothSite B) J K
    (U := U) (X := X) j ((toSheaf k).obj F) n
    (isIso_refinementSheafAdjunction_counit_of_le.{u + 1}
      J K (SmoothSite.zariskiTopology_le_nisnevichTopology B) ((toSheaf k).obj F))

end AlgebraicGeometry.SheafWithTransfers
