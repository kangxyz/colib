/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowTransformationCylinder
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality

/-! # Whole input naturality of the first-row transformation cylinder

Both original interval coordinates are retained. Precomposition acts on the input
finite S-diagram, before the transformation and the original first-row insertion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {V W T : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

/-- The complete first-row simplex preserves the actual input map and both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationInputNaturality.lean:28"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem rowTransformationSimplex_precomp (J : T ⟶ V) (k : ℕ)
    (n : SimplexCategoryᵒᵖ) (A : ((stages k).obj T).obj n) (τ θ : (Δ[1] : SSet.{u}).obj n) :
    rowTransformationSimplex (F := J ≫ F) (G := J ≫ G)
        (whiskerLeft J.hom.toFunctor η) (fun B => hη (J.hom.toFunctor.obj B)) k n A τ θ =
      rowTransformationSimplex η hη k n (((stages k).map J).app n A) τ θ := by
  exact (rowTransformationSimplex_eq (F := J ≫ F) (G := J ≫ G)
    (whiskerLeft J.hom.toFunctor η) (fun B => hη (J.hom.toFunctor.obj B)) k n A τ θ).trans
    ((congrArg (fun z => (stageCylinder k W).app n (z, θ))
      (stageTransformationFunction_precomp k η hη J n A τ)).trans
      (rowTransformationSimplex_eq η hη k n (((stages k).map J).app n A) τ θ).symm)

/-- The whole double cylinder is natural in the original input Model map. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationInputNaturality.lean:40"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem rowTransformationCylinder_precomp (J : T ⟶ V) (k : ℕ) :
    rowTransformationCylinder (F := J ≫ F) (G := J ≫ G)
        (whiskerLeft J.hom.toFunctor η) (fun B => hη (J.hom.toFunctor.obj B)) k =
      (((stages k).map J ▷ Δ[1]) ▷ Δ[1]) ≫ rowTransformationCylinder η hη k := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact rowTransformationSimplex_precomp η hη J k n z.1.1 z.1.2 z.2

end CategoryTheory.Waldhausen.IteratedS
