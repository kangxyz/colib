/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicTopology.DoldKan.NormalizedMooreMap
public import Colib.CategoryTheory.Sites.Point.QuasiIso
public import Colib.CategoryTheory.Sites.Simplicial.ReducedChainsFiber

/-!
# Stalks of normalized reduced chains

The native abelian stalk commutes with the chosen normalized Moore complex.
Combined with the simplicial reduction comparison, it identifies the stalk
of sheafified reduced chains with normalized chains of the pointed fiber.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  [LocallySmall.{w} C] [HasSheafify J AddCommGrpCat.{w}]

/-- The native abelian stalk of sheafified normalized reduced chains agrees
naturally with normalized reduction of the actual pointed simplicial fiber. -/
def sheafifiedReducedChainsFiberIso :
    sheafifiedReducedChains C J ⋙
        (Φ.sheafFiber (A := AddCommGrpCat.{w})).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      reducedFreeAbelianFiber Φ ⋙ normalizedMooreComplex AddCommGrpCat.{w} :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (normalizedMooreComplexCompMapHomologicalComplexIso
      (Φ.sheafFiber (A := AddCommGrpCat.{w}))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafifiedReducedFreeAbelianFiberIso Φ) _

variable [J.HasEnoughPoints.{w}]

/-- Enough points detect quasi-isomorphisms of the reduced chain map on the normalized fibers. -/
theorem quasiIso_sheafifiedReducedChains_map_iff
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    QuasiIso ((sheafifiedReducedChains C J).map f) ↔
      ∀ Φ : J.Point.{w}, QuasiIso
        ((reducedFreeAbelianFiber Φ ⋙ normalizedMooreComplex AddCommGrpCat.{w}).map f) := by
  rw [GrothendieckTopology.Point.quasiIso_iff_forall_sheafFiber]
  refine forall_congr' fun Φ ↦ ?_
  let e := sheafifiedReducedChainsFiberIso Φ
  exact (HomologicalComplex.quasiIso AddCommGrpCat.{w} (ComplexShape.down ℕ)).arrow_mk_iso_iff
    (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)

attribute [colib_ref "mathlib_dold_kan_pin"
  "Mathlib/AlgebraicTopology/DoldKan/Normalized.lean:81-121" "ingredient"
  "The two normalized Moore splittings identify normalization before and after taking the fiber"]
  sheafifiedReducedChainsFiberIso

end CategoryTheory.PointedSimplicialPresheaf

namespace CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-1011"]
  sheafifiedReducedChainsFiberIso
  quasiIso_sheafifiedReducedChains_map_iff

end CategoryTheory.PointedSimplicialPresheaf
