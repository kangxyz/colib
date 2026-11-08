/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.SeparatedPairMap
public import Colib.KTheory.Waldhausen.Additivity.DiagonalKMap
public import Colib.KTheory.Waldhausen.Additivity.SubdivisionBasepoint
public import Colib.KTheory.Waldhausen.Product.KEquivalence

/-! # The actual pair of distinct subdivision restrictions

The old separated pair grid is a genuine product Waldhausen grid in both independent degrees.
Its two projections are the original first and right restrictions. The actual diagonal and
product realization maps preserve those projections and the chosen zero, without any inverse
or compact-lift choice.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Additivity/SeparatedPairMap.lean:105-165`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both restrictions remain distinct. -/
@[expose] public section
open SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
open Product
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The original first restriction followed by its actual diagonal isomorphism. -/
def separatedFirstDeloopingMap :
    C(|SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|, V.Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom.comp
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))

/-- The original right restriction followed by that same diagonal isomorphism. -/
def separatedRightDeloopingMap :
    C(|SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|, V.Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom.comp
    (realizedDiagonalMap (rightRestrictionMap V))

/-- The actual product-valued map on the unchanged original subdivision realization. -/
def separatedPairDeloopingMap :
    C(|SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      (productStructure V V).Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso (productStructure V V)).hom).hom.comp
    (realizedDiagonalMap (separatedPairMap V))

/-- Both actual product projections retain the distinct original restriction maps. -/
theorem separatedPairDeloopingMap_projection
    (x : |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    Product.deloopingComparison V V (separatedPairDeloopingMap V x) =
      (separatedFirstDeloopingMap V x, separatedRightDeloopingMap V x) := by
  apply _root_.Prod.ext
  · have hn := DFunLike.congr_fun
      (realizedDiagonalMap_exact_naturality (productStructure V V) V (fst_exact V V))
      (realizedDiagonalMap (separatedPairMap V) x)
    have hp := DFunLike.congr_fun (congrArg realizedDiagonalMap (separatedPairMap_fst V)) x
    rw [realizedDiagonalMap_comp] at hp
    exact hn.symm.trans (congrArg
      (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y) hp)
  · have hn := DFunLike.congr_fun
      (realizedDiagonalMap_exact_naturality (productStructure V V) V (snd_exact V V))
      (realizedDiagonalMap (separatedPairMap V) x)
    have hp := DFunLike.congr_fun (congrArg realizedDiagonalMap (separatedPairMap_snd V)) x
    rw [realizedDiagonalMap_comp] at hp
    exact hn.symm.trans (congrArg
      (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y) hp)

/-- The first restriction retains its original chosen-zero point. -/
theorem separatedFirstDeloopingMap_basepoint :
    separatedFirstDeloopingMap V (subdivisionBasepoint V) = V.kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y)
    (horizontalEndpoint_basepoint V)).trans (diagonalRealization_basepoint V)

/-- The right restriction also retains that actual chosen-zero point. -/
theorem separatedRightDeloopingMap_basepoint :
    separatedRightDeloopingMap V (subdivisionBasepoint V) = V.kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y)
    (realizationPoint_naturality (SSet.diagonalMap (rightRestrictionMap V))
      (subdivisionZeroVertex V))).trans (diagonalRealization_basepoint V)

/-- The pair retains exactly the original product basepoint, with no selected path. -/
theorem separatedPairDeloopingMap_basepoint :
    separatedPairDeloopingMap V (subdivisionBasepoint V) = (productStructure V V).kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso (productStructure V V)).hom y)
    (realizationPoint_naturality (SSet.diagonalMap (separatedPairMap V))
      (subdivisionZeroVertex V))).trans (diagonalRealization_basepoint (productStructure V V))

end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/SeparatedPairMap.lean:105-165" "adaptation"
    "Distinct original first and right restrictions and their actual product map"]
  CategoryTheory.Waldhausen.Additivity.separatedPairDeloopingMap_projection
  CategoryTheory.Waldhausen.Additivity.separatedPairDeloopingMap_basepoint
