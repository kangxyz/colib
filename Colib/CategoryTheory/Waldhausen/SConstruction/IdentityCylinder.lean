/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridHomotopy
public import Colib.Util.References

/-! # The entire original identity cylinder

Every actual cut of the original identity transformation retains its full grid, including
crossing morphisms. The whole simplicial identity cylinder is the original projection
followed by the original map. Its realization is treated in KTheory.Waldhausen.IdentityCylinder.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/IdentityCylinder.lean:27-92`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe u v w w'
namespace CategoryTheory.Waldhausen
variable {D : Type u} [Category.{v} D]

/-- Every cut of the actual identity cylinder is the entire original grid. -/
theorem nerveCylinderDiagram_identity {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ D) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (𝟙 A) τ = A := by
  have h : ComposableArrows.mk₁ (𝟙 A) = (Functor.const (Fin 2)).obj A := by
    apply ComposableArrows.ext₁ (F := ComposableArrows.mk₁ (𝟙 A))
      (G := (Functor.const (Fin 2)).obj A) rfl rfl
    simp
  unfold nerveCylinderDiagram
  rw [h]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp [Functor.uncurry]

private theorem identityCylinder_map_transport {J : Type w} [Category.{w'} J]
    {F G : J ⥤ D} (h : F = G) {p q : J} (f : p ⟶ q) :
    eqToHom (congrArg (fun T ↦ T.obj p) h).symm ≫ F.map f ≫
      eqToHom (congrArg (fun T ↦ T.obj q) h) = G.map f := by
  subst G
  simp

/-- Arbitrary crossing-compatible grid arrows retain both exact object transports. -/
theorem nerveCylinderDiagram_identity_map {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ D) (τ : m ⟶ ⦋1⦌) {p q : Grid₂ n m} (f : p ⟶ q) :
    eqToHom (congrArg (fun T ↦ T.obj p) (nerveCylinderDiagram_identity A τ)).symm ≫
        (nerveCylinderDiagram (𝟙 A) τ).map f ≫
        eqToHom (congrArg (fun T ↦ T.obj q) (nerveCylinderDiagram_identity A τ)) = A.map f :=
  identityCylinder_map_transport (nerveCylinderDiagram_identity A τ) f

/-- Both independent original reindexings retain the literal transformed cut. -/
theorem nerveCylinderDiagram_identity_reindex {n n' m m' : SimplexCategory}
    (A : Grid₂ n m ⥤ D) (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (𝟙 (gridMap₂ α β ⋙ A)) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveCylinderDiagram (𝟙 A) τ := by
  rw [nerveCylinderDiagram_identity, nerveCylinderDiagram_identity]

private theorem identityCylinder_identity_heq {p q : D} (h : p = q) :
    HEq (𝟙 p) (𝟙 q) := by
  subst q
  rfl

variable (W : Structure D) {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f : X ⟶ bisimplicialSSet W)

/-- Identity-family compatibility uses the actual original diagonal grid reindexing. -/
theorem diagonalWeakGridIdentityFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (ρ : n ⟶ n') (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop) :
    HEq (NatTrans.app (𝟙 ((((f.app n').app n') ((SSet.diagonalSSet X).map ρ x)).1)) p)
      (NatTrans.app (𝟙 ((((f.app n).app n) x).1)) ((gridMap₂ ρ.unop ρ.unop).obj p)) := by
  apply identityCylinder_identity_heq
  exact congrArg (fun T ↦ T.obj p) (diagonalGridMap_reindex W f ρ x)

/-- The actual old weak-grid constructor, applied to its literal identity family. -/
def diagonalWeakGridIdentityHomotopy :
    SSet.Homotopy (SSet.diagonalMap f) (SSet.diagonalMap f) :=
  diagonalWeakGridHomotopy W f f (fun n m x ↦ 𝟙 ((((f.app n).app m) x).1))
    (fun _ _ _ _ ↦ W.weq.id_mem _) (diagonalWeakGridIdentityFamily_reindex W f)

/-- The entire old simplicial identity cylinder is the original projection followed by f. -/
theorem diagonalWeakGridIdentityHomotopy_cylinder :
    (diagonalWeakGridIdentityHomotopy W f).h =
      CartesianMonoidalCategory.fst (SSet.diagonalSSet X) Δ[1] ≫
        SSet.diagonalMap f := by
  ext n z
  apply Subtype.ext
  exact nerveCylinderDiagram_identity _ z.2.down


end CategoryTheory.Waldhausen

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/SConstruction/IdentityCylinder.lean:27-92"
    "adaptation"
    "All grid cuts, crossing arrows and reindexings of the actual identity cylinder"]
  CategoryTheory.Waldhausen.nerveCylinderDiagram_identity
  CategoryTheory.Waldhausen.nerveCylinderDiagram_identity_map
  CategoryTheory.Waldhausen.nerveCylinderDiagram_identity_reindex
  CategoryTheory.Waldhausen.diagonalWeakGridIdentityHomotopy_cylinder
