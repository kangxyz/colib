/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.StructureHomotopy

/-!
# Finite S-construction of a transformation followed by a first row

Apply each original finite S-construction to a weak natural transformation after the actual
one-row insertion. These independently specified simplex functions assemble to the double
cylinder. The whole result agrees with the original transformation cylinder followed by the
original row cylinder, retaining both interval coordinates in their specified order.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory SSet Topology
variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

/-- Apply the genuine finite S-construction after the actual first-row insertion. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationCylinder.lean:30"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
def rowTransformationSimplex (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    ((stages (k + 1)).obj W).obj n :=
  stageTransformationFunction k
    (F := F ≫ (insertion θ.down).app W) (G := G ≫ (insertion θ.down).app W)
    (whiskerRight η ((insertion θ.down).app W).hom.toFunctor)
    (fun B => ((insertion θ.down).app W).hom.isExact.weak _ (hη B)) n A τ

/-- Finite S-prolongation preserves the whole transformation/first-row composite. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationCylinder.lean:39"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
theorem rowTransformationSimplex_eq (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    rowTransformationSimplex η hη k n A τ θ =
      (stageCylinder k W).app n (stageTransformationFunction k η hη n A τ, θ) :=
  stageTransformationFunction_postcomp k η hη ((insertion θ.down).app W) n A τ

/-- The original entrywise row-transformation cells assemble under all diagonal operators. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationCylinder.lean:46"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
def rowTransformationCylinder (k : ℕ) :
    (((stages k).obj V) ⊗ Δ[1]) ⊗ Δ[1] ⟶ (stages (k + 1)).obj W where
  app n := ↾fun z => rowTransformationSimplex η hη k n z.1.1 z.1.2 z.2
  naturality n m α := by
    let H := (stageTransformationCylinder k η hη ▷ Δ[1]) ≫ stageCylinder k W
    have h (q : SimplexCategoryᵒᵖ) :
        (↾fun z : ((((stages k).obj V) ⊗ Δ[1]) ⊗ Δ[1]).obj q =>
          rowTransformationSimplex η hη k q z.1.1 z.1.2 z.2) = H.app q := by
      apply ConcreteCategory.hom_ext
      intro z
      exact rowTransformationSimplex_eq η hη k q z.1.1 z.1.2 z.2
    rw [h m, h n]
    exact H.naturality α

/-- The whole double cylinder agrees with the original ordered composite. -/
@[colib_tag "COL-0530", colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationCylinder.lean:61"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
theorem rowTransformationCylinder_eq (k : ℕ) :
    rowTransformationCylinder η hη k =
      (stageTransformationCylinder k η hη ▷ Δ[1]) ≫ stageCylinder k W := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact rowTransformationSimplex_eq η hη k n z.1.1 z.1.2 z.2

end CategoryTheory.Waldhausen.IteratedS
