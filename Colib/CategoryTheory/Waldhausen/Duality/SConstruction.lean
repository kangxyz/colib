/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Duality.Basic
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.Topology.Realization.Opposite
public import Colib.Topology.Realization.MapWeakEquivalence

/-! # Actual S-construction reversal for compatible dual Waldhausen structures

Compatibility is stated on original zero-corner squares: an actual cofibration
cofiber square is exactly a dual cofibration fiber square. No comparison of
K-theory is assumed. Reversal changes all three original grid coordinates.

Implementation provenance: `Quillen/Waldhausen/Duality/SConstruction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual maps, structural hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite SSet Topology
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen

namespace DualSConstruction

/-- Simultaneous nerve-coordinate and interval-coordinate reversal. -/
def reverseGrid (n : SimplexCategory) : Grid n ⥤ (Grid n)ᵒᵖ where
  obj p := op (grid p.1.rev p.2.1.2.rev p.2.1.1.rev (Fin.rev_le_rev.mpr p.2.2))
  map f := (homOfLE (show grid _ _ _ _ ≤ grid _ _ _ _ from
    ⟨Fin.rev_le_rev.mpr (leOfHom f).1,
      Fin.rev_le_rev.mpr (leOfHom f).2.2,
      Fin.rev_le_rev.mpr (leOfHom f).2.1⟩)).op

variable {C : Type u} [Category.{v} C]

/-- Reverse the actual grid diagram, retaining all its arrows in the opposite category. -/
def reverseOp {n : SimplexCategory} (F : Grid n ⥤ C) : Grid n ⥤ Cᵒᵖ :=
  reverseGrid n ⋙ F.op

/-- Inverse reversal on an actual opposite-category grid diagram. -/
def reverseUnop {n : SimplexCategory} (F : Grid n ⥤ Cᵒᵖ) : Grid n ⥤ C :=
  reverseGrid n ⋙ F.leftOp

@[simp] theorem reverseOp_obj {n} (F : Grid n ⥤ C) (t i j) (hij : i ≤ j) :
    (reverseOp F).obj (grid t i j hij) =
      op (F.obj (grid t.rev j.rev i.rev (Fin.rev_le_rev.mpr hij))) := rfl

@[simp] theorem reverseUnop_obj {n} (F : Grid n ⥤ Cᵒᵖ) (t i j) (hij : i ≤ j) :
    (reverseUnop F).obj (grid t i j hij) =
      unop (F.obj (grid t.rev j.rev i.rev (Fin.rev_le_rev.mpr hij))) := rfl

@[simp] theorem reverseGrid_involutive (n : SimplexCategory) :
    reverseGrid n ⋙ (reverseGrid n).leftOp = 𝟭 (Grid n) := by
  refine CategoryTheory.Functor.ext (fun p => ?_) ?_
  · simp [reverseGrid, grid, interval]
  · intros; apply Subsingleton.elim

@[simp] theorem reverseUnop_reverseOp {n} (F : Grid n ⥤ C) :
    reverseUnop (reverseOp F) = F := by
  change (reverseGrid n ⋙ (reverseGrid n).leftOp) ⋙ F = F
  rw [reverseGrid_involutive]
  rfl

@[simp] theorem reverseOp_reverseUnop {n} (F : Grid n ⥤ Cᵒᵖ) :
    reverseOp (reverseUnop F) = F := by
  change (reverseGrid n ⋙ (reverseGrid n).leftOp) ⋙ F = F
  rw [reverseGrid_involutive]
  rfl

/-- Coordinate reversal conjugates each original simplex operator. -/
theorem reverseGrid_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    gridMap α ⋙ reverseGrid n = reverseGrid m ⋙ (gridMap (SimplexCategory.rev.map α)).op := by
  refine CategoryTheory.Functor.ext (fun p => ?_) ?_
  · apply unop_injective
    simp [reverseGrid, gridMap, grid, interval, SimplexCategory.rev_map_apply]
  · intros; apply Subsingleton.elim

/-- Reversal commutes with restriction after reversing the simplex operator. -/
theorem reverseOp_precomp {m n : SimplexCategory} (α : m ⟶ n) (F : Grid n ⥤ C) :
    reverseOp (gridMap (SimplexCategory.rev.map α) ⋙ F) = gridMap α ⋙ reverseOp F := by
  change (reverseGrid m ⋙ (gridMap (SimplexCategory.rev.map α)).op) ⋙ F.op =
    (gridMap α ⋙ reverseGrid n) ⋙ F.op
  rw [reverseGrid_naturality]

variable {W : Structure C} {Wd : Structure Cᵒᵖ} (h : IsCompatibleDual W Wd)

include h

/-- Actual cofiber squares become actual opposite cofiber squares. -/
theorem isSimplex_reverseOp {n} {F : Grid n ⥤ C} (hF : IsSimplex W.cof W.weq F) :
    IsSimplex Wd.cof Wd.weq (reverseOp F) where
  zero t i := (hF.zero t.rev i.rev).op
  cofibration t i j k hij hjk :=
    ((h.cofiber _ _ _ _ (hF.zero t.rev j.rev)).mp
      ⟨hF.cofibration t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij),
       hF.quotient t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij)⟩).1
  quotient t i j k hij hjk :=
    ((h.cofiber _ _ _ _ (hF.zero t.rev j.rev)).mp
      ⟨hF.cofibration t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij),
       hF.quotient t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij)⟩).2.op.flip
  weak s t i j hst hij := (h.weak _).mp
    (hF.weak t.rev s.rev j.rev i.rev (Fin.rev_le_rev.mpr hst)
      (Fin.rev_le_rev.mpr hij))

/-- Reverse an actual dual cofiber square back into its original cofiber square. -/
theorem isSimplex_reverseUnop {n} {F : Grid n ⥤ Cᵒᵖ}
    (hF : IsSimplex Wd.cof Wd.weq F) :
    IsSimplex W.cof W.weq (reverseUnop F) where
  zero t i := (hF.zero t.rev i.rev).unop
  cofibration t i j k hij hjk :=
    ((h.cofiber _ _ _ _ (hF.zero t.rev j.rev).unop).mpr
      ⟨hF.cofibration t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij),
       (hF.quotient t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij)).unop.flip⟩).1
  quotient t i j k hij hjk :=
    ((h.cofiber _ _ _ _ (hF.zero t.rev j.rev).unop).mpr
      ⟨hF.cofibration t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij),
       (hF.quotient t.rev k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
        (Fin.rev_le_rev.mpr hij)).unop.flip⟩).2
  weak s t i j hst hij := (h.weak _).mpr
    (hF.weak t.rev s.rev j.rev i.rev (Fin.rev_le_rev.mpr hst)
      (Fin.rev_le_rev.mpr hij))

/-- The original dual S-construction is the opposite simplicial set, by literal
reversal of every original grid coordinate and every original arrow. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Duality/SConstruction.lean:136-147" "adaptation"
    "Whole simplicial comparison by literal three-coordinate grid reversal"]
def sSetIso : (sSet W.cof W.weq).op ≅ sSet Wd.cof Wd.weq :=
  NatIso.ofComponents (fun n => Equiv.toIso {
    toFun := fun F => ⟨reverseOp F.val, isSimplex_reverseOp h F.property⟩
    invFun := fun F => ⟨reverseUnop F.val, isSimplex_reverseUnop h F.property⟩
    left_inv := fun F => Subtype.ext (reverseUnop_reverseOp F.val)
    right_inv := fun F => Subtype.ext (reverseOp_reverseUnop F.val) }) (by
      intro m n α
      ext F : 3
      apply Subtype.ext
      exact reverseOp_precomp α.unop F.val)

/-- The isomorphism retains the original component diagram, not an abstract replacement. -/
@[simp] theorem sSetIso_hom_app (n : SimplexCategoryᵒᵖ)
    (F : (sSet W.cof W.weq).op.obj n) :
    ((sSetIso h).hom.app n F).val = reverseOp F.val := rfl

/-- Original realizations are homeomorphic by the explicit grid reversal and
actual simplex-coordinate reversal. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Duality/SConstruction.lean:154-158" "adaptation"
    "The actual realization homeomorphism induced by grid and simplex reversal"]
def realizationHomeomorph : |sSet W.cof W.weq| ≃ₜ |sSet Wd.cof Wd.weq| :=
  (realizationOppositeHomeomorph _).symm.trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (sSetIso h)))

variable {D : Type u} [Category.{v} D] {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hV : IsCompatibleDual V Vd) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)

/-- The reversal isomorphisms intertwine the actual original exact functor maps. -/
theorem sSetIso_naturality :
    SSet.opFunctor.map (sSetMap hF) ≫ (sSetIso hV).hom =
      (sSetIso h).hom ≫ sSetMap hFd := by
  ext n A : 4
  rfl

include hV
/-- Dual weakness transfers to the literal original S-map. No basepoint
identification or weak-to-homotopy-equivalence upgrade is required. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Duality/SConstruction.lean:173-191" "adaptation"
    "Weakness transfers to the unchanged original exact-functor S-map"]
theorem sSetMap_weak_of_dual (hd : IsRealizationWeakEquivalence (sSetMap hFd)) :
    IsRealizationWeakEquivalence (sSetMap hF) := by
  have hop := IsRealizationWeakEquivalence.of_iso_square
    (SSet.opFunctor.map (sSetMap hF)) (sSetMap hFd)
    (sSetIso h) (sSetIso hV) (sSetIso_naturality h hV hF hFd) hd
  have hA := isWeakHomotopyEquivalence_of_homotopyEquiv
    (realizationOppositeHomeomorph (sSet W.cof W.weq)).toHomotopyEquiv
  have hB := isWeakHomotopyEquivalence_of_homotopyEquiv
    (realizationOppositeHomeomorph (sSet V.cof V.weq)).toHomotopyEquiv
  have hw := congrArg TopCat.Hom.hom (realizationOpposite_naturality (sSetMap hF))
  simp only [TopCat.hom_comp] at hw
  have hh := hB.comp hop
  change IsWeakHomotopyEquivalence
    (((realizationOppositeNatIso.app (sSet V.cof V.weq)).hom).hom.comp
      (SSet.toTop.map (SSet.opFunctor.map (sSetMap hF))).hom) at hh
  rw [hw] at hh
  exact hh.of_comp_left hA

end DualSConstruction
end CategoryTheory.Waldhausen
