/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagramStableEquivalence

/-! # Stable preservation by the original finite Bass iteration -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C]

/-- Every original iterate preserves the same stable arrow, using proved topology/growth closure. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramStableEquivalence.lean:111"
  "adaptation" "Original finite Bass preservation and actual exact-equivalence maps"]
theorem strictDiagramIterate_map_isStableEquivalence_of_linearGrowth
    (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (F G : C ⥤ LoopPrespectrum.{w})
    [∀ X m, T1Space ((F.obj X).space m)] [∀ X m, T1Space ((G.obj X).space m)]
    (hF : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (hG : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((G.obj X).point m))))
    (c d : ℕ)
    (hπF : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (hπG : ∀ X n k, k < n + 2 → ∀ x : (G.obj X).space (n + d + 2),
      Subsingleton (HomotopyGroup.Pi k ((G.obj X).space (n + d + 2)) x))
    (η : F ⟶ G) (hη : ∀ X, IsStableEquivalence (η.app X)) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map η).app X) := by
  induction i generalizing F G c d with
  | zero => exact hη X
  | succ i ih =>
    exact ih ((strictDiagramFunctor Q).obj F) ((strictDiagramFunctor Q).obj G)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q F hF)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q G hG) (c + 1) (d + 1)
      (strictDiagramFunctor_homotopyGroup_subsingleton Q F hF c hπF)
      (strictDiagramFunctor_homotopyGroup_subsingleton Q G hG d hπG)
      ((strictDiagramFunctor Q).map η)
      (strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth Q F G hF hG c d hπF hπG η hη)

end KTheory.Bass
