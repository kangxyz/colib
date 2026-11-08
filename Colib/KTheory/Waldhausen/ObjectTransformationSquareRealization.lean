/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.ObjectTransformationSquare
public import Colib.KTheory.Waldhausen.BisimplexRealization
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectLoops
public import Colib.KTheory.Waldhausen.WeakNaturalTransformation
public import Colib.Topology.Realization.HomotopyBridge

/-! # Exact continuous coordinates of the original object transformation cylinder

Evaluation on the original canonical object loop is the original component weak-arrow square,
with the loop and transformation coordinates retained in that order. The existing inverse
product-simplex and cylinder comparisons supply the equality of the actual continuous maps.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/SConstruction/ObjectTransformationSquareRealization.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Convexity
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF0 hG0 in
/-- The actual transformation on the original object loop is its full component weak square. -/
theorem objectTransformationRealization_square (A : C) (s t : unitInterval) :
    weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A t) =
      bisimplexRealization W (W.weakObjectSimplex (η.app A) (hη A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (η.app A) (hη A)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) := by
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality
      (SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A))) (realizationInterval t, ULift.up s)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A) ▷ Δ[1])
      ((realizationCylinderIso (Δ[1] : SSet.{max u v})).inv
        (realizationInterval t, ULift.up s)) =
    (realizationCylinderIso (sSet V.cof V.weq)).inv
      (SSet.toTop.map (SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A))
        (realizationInterval t), ULift.up s) at hn
  change SSet.toTop.map (weakNaturalTransformationCylinder V W hF hG η hη)
      ((realizationCylinderIso (sSet V.cof V.weq)).inv
        (SSet.toTop.map (SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A))
          (realizationInterval t), ULift.up s)) = _
  rw [← hn]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A) ▷ Δ[1]) ≫
    SSet.toTop.map (weakNaturalTransformationCylinder V W hF hG η hη)) _ = _
  rw [← Functor.map_comp, objectTransformationCylinder_square V W hF hG η hη hF0 hG0]
  have he : realizationProductSimplexIso (Δ[1] : SSet.{max u v}) 1 ≪≫
      MonoidalCategory.whiskerLeftIso |(Δ[1] : SSet.{max u v})|
        SSet.stdSimplex.toTopObjIsoI = realizationCylinderIso Δ[1] := by
    apply Iso.ext
    change CartesianMonoidalCategory.prodComparison SSet.toTop
        (Δ[1] : SSet.{max u v}) (Δ[1] : SSet.{max u v}) ≫
        (|(Δ[1] : SSet.{max u v})| ◁ SSet.stdSimplex.toTopObjIsoI.hom) =
      realizationCylinderComparison (Δ[1] : SSet.{max u v})
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [realizationCylinderComparison]
  have hp := ConcreteCategory.congr_hom (congrArg Iso.inv he)
    (realizationInterval t, ULift.up s)
  change (realizationProductSimplexIso (Δ[1] : SSet.{max u v}) 1).inv
      (realizationInterval t, realizationInterval s) =
    (realizationCylinderIso (Δ[1] : SSet.{max u v})).inv
      (realizationInterval t, ULift.up s) at hp
  rw [← hp]
  rfl

end CategoryTheory.Waldhausen
