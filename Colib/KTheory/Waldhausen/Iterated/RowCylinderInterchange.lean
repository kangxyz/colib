/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Interchange
public import Colib.Topology.Realization.DoubleHomotopy
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-!
# The actual row interchange on two original S-cylinders

The genuine quotient-row transpose acts on the diagonal double prolongation of any simplicial
invariant. Its naturality retains both ordinal restrictions. The original one-row insertion
square gives the full two-cylinder comparison, with the two interval directions explicitly
swapped. This is a finite row/structure identity; no normalization homotopy is inferred from it.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/RowCylinderInterchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
row transpose, based maps, independent time coordinates and hypotheses are retained.
The existing native wide category of zero-preserving exact maps supplies the original models. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- Restrict the two original row directions by the same displayed ordinal map. -/
def diagonalRowsReindex (W : WideSubcategory preservesZero.{u})
    {m n : SimplexCategory} (α : m ⟶ n) :
    (rows n).obj ((rows n).obj W) ⟶ (rows m).obj ((rows m).obj W) :=
  (rows n).map ((rowsReindex α).app W) ≫
    (rowsReindex α).app ((rows m).obj W)

/-- The actual row transpose commutes with both original ordinal restrictions. -/
theorem rowSwap_diagonalReindex (W : WideSubcategory preservesZero.{u})
    {m n : SimplexCategory} (α : m ⟶ n) :
    (rowSwap W n n).hom ≫ diagonalRowsReindex W α =
      diagonalRowsReindex W α ≫ (rowSwap W m m).hom := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- The whole exact insertion square, including the displayed coefficient/structure row swap. -/
theorem insertion_insertion_rowSwap (W : WideSubcategory preservesZero.{u}) {m n : SimplexCategory}
    (θ : m ⟶ ⦋1⦌) (τ : n ⟶ ⦋1⦌) :
    ((insertion θ).app W ≫ (rows m).map ((insertion τ).app W)) ≫
      (rowSwap W m n).hom =
        (insertion τ).app W ≫ (rows n).map ((insertion θ).app W) := by
  rw [Category.assoc, insertion_rowSwap]
  exact (insertion τ).naturality ((insertion θ).app W)

/-- Double diagonal restriction is the original two-row restriction followed by H's map. -/
theorem prolong_prolong_map (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((prolong (prolong H)).obj W).map α =
      (H.map (diagonalRowsReindex W α.unop)).app n ≫
        (H.obj ((rows m.unop).obj ((rows m.unop).obj W))).map α := by
  dsimp only [diagonalRowsReindex]
  rw [H.map_comp, NatTrans.comp_app]
  rfl

/-- The diagonal row transpose on the genuine double prolongation, with actual simplex values. -/
def prolongRowSwap (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    (prolong (prolong H)).obj W ⟶ (prolong (prolong H)).obj W where
  app n := ((H.map (rowSwap W n.unop n.unop).hom).app n)
  naturality n m α := by
    let R := diagonalRowsReindex W α.unop
    let V := (rows m.unop).obj ((rows m.unop).obj W)
    have hR : H.map (rowSwap W n.unop n.unop).hom ≫ H.map R =
        H.map R ≫ H.map (rowSwap W m.unop m.unop).hom := by
      rw [← H.map_comp, ← H.map_comp, rowSwap_diagonalReindex]
    rw [prolong_prolong_map]
    apply ConcreteCategory.hom_ext
    intro A
    change (H.map (rowSwap W m.unop m.unop).hom).app m
        ((H.obj V).map α ((H.map R).app n A)) =
      (H.obj V).map α ((H.map R).app n
        ((H.map (rowSwap W n.unop n.unop).hom).app n A))
    have hN := ConcreteCategory.congr_hom
      ((H.map (rowSwap W m.unop m.unop).hom).naturality α) ((H.map R).app n A)
    have hA := ConcreteCategory.congr_hom (NatTrans.congr_app hR n) A
    exact hN.trans (congrArg ((H.obj V).map α) hA.symm)

/-- Two whole original cylinders interchange only after their genuine row transpose. -/
theorem prolongCylinder_rowSwap (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    (prolongCylinder H W ▷ Δ[1]) ≫ prolongCylinder (prolong H) W ≫
      prolongRowSwap H W =
        SSet.simplicialCylinderSwap (H.obj W) ≫
          (prolongCylinder H W ▷ Δ[1]) ≫ prolongCylinder (prolong H) W := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (H.map (rowSwap W n.unop n.unop).hom).app n
      ((H.map ((rows n.unop).map ((insertion z.2.down).app W))).app n
        ((H.map ((insertion z.1.2.down).app W)).app n z.1.1)) =
    (H.map ((rows n.unop).map ((insertion z.1.2.down).app W))).app n
      ((H.map ((insertion z.2.down).app W)).app n z.1.1)
  have h := congrArg H.map (insertion_insertion_rowSwap W z.1.2.down z.2.down)
  rw [H.map_comp, H.map_comp, H.map_comp] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h n) z.1.1

end CategoryTheory.Waldhausen.IteratedS
