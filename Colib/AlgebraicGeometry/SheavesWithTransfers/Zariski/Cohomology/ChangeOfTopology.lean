/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.DerivedSections
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # The canonical cohomology presheaf comparison for a change of topology

For the continuous identity functor from the coarser site to the finer
one, the edge map for direct image and the inclusion of sheaves into
presheaves is the comparison of cohomology presheaves in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology

universe t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J K : GrothendieckTopology C)
  [(𝟭 C).IsContinuous J K]

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => AddCommGrpCat.{max u v t}
set_option quotPrecheck false in
local notation "P" => (𝟭 C).sheafPushforwardContinuous A J K
local notation "L" => sheafToPresheaf J A ⋙ presheafToSheaf K A

variable [HasSheafify K A]

private def coarseningAdjunction : L ⊣ P :=
  (sheafificationAdjunction K A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

private theorem coarsening_preservesFiniteLimits : PreservesFiniteLimits P := by
  let := (coarseningAdjunction.{t} J K).isRightAdjoint
  infer_instance

private theorem coarsening_preservesInjectiveObjects : (P).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (coarseningAdjunction.{t} J K)

variable [HasSheafify J A] [HasExt.{max u v t} (Sheaf J A)] [HasExt.{max u v t} (Sheaf K A)]
  [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf K A)]

/-- The canonical coarser-to-finer cohomology map, in the actual cohomology presheaves.
Its middle factor is the edge morphism for the direct image followed by the sheaf inclusion. -/
@[no_expose]
def cohomologyPresheafChangeOfTopology (n : ℕ) :
    P ⋙ cohomologyPresheafFunctor.{max u v t, max u t} J n ⟶
      cohomologyPresheafFunctor.{max u v t, max u t} K n := by
  letI := coarsening_preservesInjectiveObjects.{t} J K
  exact Functor.whiskerLeft P (cohomologyPresheafFunctorIsoRightDerived.{t} J n).hom ≫
    RightDerivedEdge.edge P (sheafToPresheaf J A) n ≫
    (cohomologyPresheafFunctorIsoRightDerived.{t} K n).inv

omit [HasExt.{max u v t} (Sheaf J A)] [EnoughInjectives (Sheaf J A)] in
/-- The higher direct image for a change of topology vanishes if the corresponding
cohomology presheaf sheafifies to zero on the coarser site. -/
theorem isZero_rightDerived_changeOfTopology_of_isZero_sheafify_cohomology
    (F : Sheaf K A) (n : ℕ)
    (h : IsZero ((presheafToSheaf J A).obj (cohomologyPresheaf.{max u v t, max u t} F n))) :
    IsZero (((P).rightDerived n).obj F) := by
  let e := (SheafifiedHigherDirectImage.rightDerivedPushforwardIso
    (J := J) (K := K) A (𝟭 C) n).app F
  exact h.of_iso (e ≪≫ (presheafToSheaf J A).mapIso
    ((cohomologyPresheafFunctorIsoRightDerived.{t} K n).app F).symm)

/-- The canonical comparison is invertible when the positive higher direct images through
that degree vanish. -/
theorem isIso_cohomologyPresheafChangeOfTopology_app (F : Sheaf K A) (n : ℕ)
    (h : ∀ q, 1 ≤ q → q ≤ n → IsZero (((P).rightDerived q).obj F)) :
    IsIso ((cohomologyPresheafChangeOfTopology.{t} J K n).app F) := by
  let := coarsening_preservesFiniteLimits.{t} J K
  let := coarsening_preservesInjectiveObjects.{t} J K
  have hEdge := RightDerivedEdgeIso.isIso_edge_app P (sheafToPresheaf J A) F n h
  exact IsIso.comp_isIso'
    ((cohomologyPresheafFunctorIsoRightDerived.{t} J n).app ((P).obj F)).isIso_hom
    (IsIso.comp_isIso' hEdge ((cohomologyPresheafFunctorIsoRightDerived.{t} K n).app F).isIso_inv)

end Stacks.Cohomology.FreeYonedaUnivLE
