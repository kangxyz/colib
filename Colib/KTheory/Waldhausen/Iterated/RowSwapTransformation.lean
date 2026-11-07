/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowCylinderRealization
public import Colib.KTheory.Waldhausen.Iterated.StructureHomotopy

/-!
# Genuine row interchange preserves the original transformation cylinders

Two entrywise quotient-row transformations commute with the actual transpose, including their
endpoint identifications. Applying the original finite S-construction gives a full simplicial
cylinder square. Its realization retains the entire transformation time. These identities are
needed before transporting original comparison fillers and nulls across a row refinement.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/RowSwapTransformation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
finite simplices, complete cylinders, independent time coordinates and endpoint casts are retained.
The existing native wide category of zero-preserving exact maps supplies the original models. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}

/-- Entrywise weak transformations commute with the whole original row transpose. -/
theorem rowsTransformation_rowSwap_square (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (m n : SimplexCategory) :
    whiskerRight (rowsTransformation (rowsTransformation η n) m) (rowSwap W m n).hom.hom.toFunctor ≫
      eqToHom (congrArg (fun f ↦ f.hom.toFunctor) ((rowsInterchange m n).hom.naturality G)) =
    eqToHom (congrArg (fun f ↦ f.hom.toFunctor) ((rowsInterchange m n).hom.naturality F)) ≫
      whiskerLeft (rowSwap V m n).hom.hom.toFunctor (rowsTransformation (rowsTransformation η m) n)
      := by
  ext A : 2
  apply ObjectProperty.hom_ext
  ext p
  apply ObjectProperty.hom_ext
  ext q
  simp only [NatTrans.comp_app, eqToHom_app, whiskerRight_app, whiskerLeft_app]
  change η.app ((A.obj.obj q).obj.obj p) ≫ 𝟙 _ =
    𝟙 _ ≫ η.app ((A.obj.obj q).obj.obj p)
  simp only [Category.comp_id, Category.id_comp]

/-- Every finite transformation simplex respects the genuine swap of its last two rows. -/
theorem stageTransformationFunction_rowSwap (k : ℕ) (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (n : SimplexCategoryᵒᵖ)
    (A : ((stages (k + 2)).obj V).obj n) (τ : (Δ[1]).obj n) :
    (prolongRowSwap (stages k) W).app n
      (stageTransformationFunction (k + 2) η hη n A τ) =
    stageTransformationFunction (k + 2) η hη n
      ((prolongRowSwap (stages k) V).app n A) τ := by
  change ((stages k).map (rowSwap W n.unop n.unop).hom).app n
      (stageTransformationFunction k (rowsTransformation (rowsTransformation η n.unop) n.unop)
        _ n A τ) =
    stageTransformationFunction k (rowsTransformation (rowsTransformation η n.unop) n.unop)
      _ n (((stages k).map (rowSwap V n.unop n.unop).hom).app n A) τ
  rw [← stageTransformationFunction_postcomp, ← stageTransformationFunction_precomp]
  exact stageTransformationFunction_congr k
    ((rowsInterchange n.unop n.unop).hom.naturality F)
    ((rowsInterchange n.unop n.unop).hom.naturality G) _ _ _ _
    (rowsTransformation_rowSwap_square η n.unop n.unop) n A τ

/-- The entire original transformation cylinder commutes with the actual row swap. -/
theorem stageTransformationCylinder_rowSwap (k : ℕ) (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    stageTransformationCylinder (k + 2) η hη ≫ prolongRowSwap (stages k) W =
      (prolongRowSwap (stages k) V ▷ Δ[1]) ≫ stageTransformationCylinder (k + 2) η hη := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact stageTransformationFunction_rowSwap k η hη n z.1 z.2

/-- Realized row interchange retains the complete original weak-transformation track. -/
theorem stageTransformationTopHomotopy_rowSwap (k : ℕ) (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (t : unitInterval)
    (x : stageSpace (k + 2) V) :
    stageRowSwapHomeomorph k W (stageTransformationTopHomotopy (k + 2) η hη (t, x)) =
      stageTransformationTopHomotopy (k + 2) η hη (t, stageRowSwapHomeomorph k V x) :=
  realizationSimplicialHomotopy_square (stageTransformationHomotopy (k + 2) η hη)
    (stageTransformationHomotopy (k + 2) η hη) (prolongRowSwap (stages k) V)
    (prolongRowSwap (stages k) W) (stageTransformationCylinder_rowSwap k η hη) t x

end CategoryTheory.Waldhausen.IteratedS
