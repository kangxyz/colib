/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowCylinderInterchange

/-!
# Realization of the genuine two-row interchange

The original row transpose is an involutive simplicial isomorphism, natural in exact based
model maps. Its realization preserves the original stage point. The complete two-structure
formula retains both interval coordinates and the actual target row transpose. It is a finite
structure face, and does not assert spectrum compatibility for inverse-prefix normalization.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/RowCylinderRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
row transpose, based maps, independent time coordinates and hypotheses are retained.
The existing native wide category of zero-preserving exact maps supplies the original models. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- The whole diagonal row transpose is involutive. -/
theorem prolongRowSwap_comp_self (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    prolongRowSwap H W ≫ prolongRowSwap H W = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  change (H.map (rowSwap W n.unop n.unop).hom).app n ≫
      (H.map (rowSwap W n.unop n.unop).inv).app n = 𝟙 _
  rw [← NatTrans.comp_app, ← H.map_comp, Iso.hom_inv_id, H.map_id]
  rfl

/-- The actual row transpose is a simplicial isomorphism, without choosing an inverse. -/
def prolongRowSwapIso (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    (prolong (prolong H)).obj W ≅ (prolong (prolong H)).obj W where
  hom := prolongRowSwap H W
  inv := prolongRowSwap H W
  hom_inv_id := prolongRowSwap_comp_self H W
  inv_hom_id := prolongRowSwap_comp_self H W

/-- The entire row transpose is natural in the original exact based model map. -/
theorem prolongRowSwap_naturality (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    (prolong (prolong H)).map F ≫ prolongRowSwap H W =
      prolongRowSwap H V ≫ (prolong (prolong H)).map F := by
  apply NatTrans.ext
  funext n
  change (H.map ((rows n.unop).map ((rows n.unop).map F))).app n ≫
      (H.map (rowSwap W n.unop n.unop).hom).app n =
    (H.map (rowSwap V n.unop n.unop).hom).app n ≫
      (H.map ((rows n.unop).map ((rows n.unop).map F))).app n
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← H.map_comp, ← H.map_comp]
  exact congrArg (fun G => (H.map G).app n) ((rowsInterchange n.unop n.unop).hom.naturality F)

/-- The row transpose fixes the specified next-next stage vertex. -/
theorem prolongRowSwap_stageVertex (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    (prolongRowSwap (stages k) W).app (op ⦋0⦌) (stageVertex (k + 2) W) =
      stageVertex (k + 2) W :=
  stageVertex_naturality k (rowSwap W ⦋0⦌ ⦋0⦌).hom

/-- The realized genuine row interchange, with its literal involutive inverse. -/
def stageRowSwapHomeomorph (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    stageSpace (k + 2) W ≃ₜ stageSpace (k + 2) W :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (prolongRowSwapIso (stages k) W))

/-- The original stage point is unchanged by the realized row transpose. -/
theorem stageRowSwapHomeomorph_point (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    stageRowSwapHomeomorph k W (stagePoint (k + 2) W) = stagePoint (k + 2) W := by
  change SSet.toTop.map (prolongRowSwap (stages k) W)
    (realizationPoint (stageVertex (k + 2) W)) = realizationPoint (stageVertex (k + 2) W)
  rw [realizationPoint_naturality, prolongRowSwap_stageVertex]

/-- Realization retains the complete two-structure equation and its actual row swap. -/
theorem stageLoopMap_rowSwap (k : ℕ) (W : WideSubcategory preservesZero.{u})
    (x : stageSpace k W) (s t : unitInterval) :
    stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W (stageLoopMap k W x s) t) =
      stageLoopMap (k + 1) W (stageLoopMap k W x t) s := by
  let A := (stages k).obj W
  let p := (SSet.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((SSet.realizationCylinderIso A).inv (x, ULift.up s), ULift.up t)
  have hs := ConcreteCategory.congr_hom
    (SSet.realizationCylinderIso_inv_naturality (stageCylinder k W))
    ((SSet.realizationCylinderIso A).inv (x, ULift.up s), ULift.up t)
  have ht := ConcreteCategory.congr_hom
    (SSet.realizationCylinderIso_inv_naturality (stageCylinder k W))
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (stageCylinder k W ▷ Δ[1]) p =
    (SSet.realizationCylinderIso ((stages (k + 1)).obj W)).inv
      (stageLoopMap k W x s, ULift.up t) at hs
  change SSet.toTop.map (stageCylinder k W ▷ Δ[1])
      ((SSet.realizationCylinderIso (A ⊗ Δ[1])).inv
        ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)) =
    (SSet.realizationCylinderIso ((stages (k + 1)).obj W)).inv
      (stageLoopMap k W x t, ULift.up s) at ht
  change SSet.toTop.map (prolongRowSwap (stages k) W)
    (SSet.toTop.map (stageCylinder (k + 1) W)
      ((SSet.realizationCylinderIso ((stages (k + 1)).obj W)).inv
        (stageLoopMap k W x s, ULift.up t))) =
    SSet.toTop.map (stageCylinder (k + 1) W)
      ((SSet.realizationCylinderIso ((stages (k + 1)).obj W)).inv
        (stageLoopMap k W x t, ULift.up s))
  rw [← hs, ← ht, ← SSet.realizationDoubleCylinderSwap_inv A x
    (ULift.up s) (ULift.up t)]
  change (SSet.toTop.map (stageCylinder k W ▷ Δ[1]) ≫
    SSet.toTop.map (stageCylinder (k + 1) W) ≫
      SSet.toTop.map (prolongRowSwap (stages k) W)) p =
    (SSet.toTop.map (SSet.simplicialCylinderSwap A) ≫
      SSet.toTop.map (stageCylinder k W ▷ Δ[1]) ≫
        SSet.toTop.map (stageCylinder (k + 1) W)) p
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun q => SSet.toTop.map q p) (prolongCylinder_rowSwap (stages k) W)

end CategoryTheory.Waldhausen.IteratedS
