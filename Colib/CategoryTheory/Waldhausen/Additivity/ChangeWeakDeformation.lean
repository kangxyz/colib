/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedDeformationMap
public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory

/-!
# The original additivity deformation under enlargement of weak equivalences

The original pushout functor and its chosen-zero normalization are independent of the target
weak predicate. This preserves every mixed cut of the displayed additivity deformation.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Additivity/ChangeWeakDeformation.lean:26-87`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open SSet.MixedOrdinalCylinder
universe u v u₁ v₁ u₂ v₂
namespace CategoryTheory.Waldhausen.Additivity

private theorem rebaseFunctor_eq_of_isZero
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (c : C) {d e : D} (hd : IsZero d) (h : d = e)
    (i : F.obj c ≅ d) (j : F.obj c ≅ e) :
    rebaseFunctor F c d i = rebaseFunctor F c e j := by
  subst e
  have hij : i = j := Iso.ext (hd.eq_of_tgt _ _)
  rw [hij]

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

include hc in
/-- The same original transformation is a cofibration for the coarse target structure. -/
theorem isCofibrationTransformation_changeWeak :
    IsCofibrationTransformation N.coarse a V := by
  have hh (X : C) : N.coarse.cof (a.app X) :=
    (congrArg (fun P : MorphismProperty D => P (a.app X)) N.cof_eq).mpr (hc.app_cof X)
  refine ⟨hh, ?_⟩
  intro X Y f hf
  exact (congrArg (fun P : MorphismProperty D =>
    P (comparison N.coarse a hh (Arrow.mk f))) N.cof_eq).mpr (hc.relative_cof f hf)

/-- The actual normalized pushout functor is unchanged under target weak enlargement. -/
theorem normalizedPushoutFunctor_changeWeak :
    normalizedPushoutFunctor V W a hF hG hc =
      normalizedPushoutFunctor V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc) := by
  unfold normalizedPushoutFunctor
  exact rebaseFunctor_eq_of_isZero (pushoutFunctor W a hc.app_cof)
    (Arrow.mk (𝟙 V.zero)) W.isZero N.zero_eq.symm _ _

/-- Every actual mixed cut retains its full original grid after weak enlargement. -/
theorem normalizedMixedGrid_changeWeak {n m : SimplexCategory} (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    normalizedMixedGrid V W a hF hG hc φ A =
      normalizedMixedGrid V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc) φ A := by
  unfold normalizedMixedGrid normalizedIntervalDiagram
  rw [normalizedPushoutFunctor_changeWeak V W N a hF hG hc]

/-- The whole original normalized mixed deformation commutes with the fine-to-coarse map. -/
theorem normalizedMixedMap_changeWeak :
    normalizedMixedMap V W a hF hG hc ≫
        bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N) =
      normalizedMixedMap V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc) := by
  ext n m s
  apply Subtype.ext
  change normalizedMixedGrid V W a hF hG hc s.1 s.2.1 ⋙ 𝟭 D = _
  rw [Functor.comp_id]
  exact normalizedMixedGrid_changeWeak V W N a hF hG hc s.1 s.2.1

end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/ChangeWeakDeformation.lean:43-87"
    "adaptation" "Actual normalized pushouts and every mixed cut under weak enlargement"]
  CategoryTheory.Waldhausen.Additivity.isCofibrationTransformation_changeWeak
  CategoryTheory.Waldhausen.Additivity.normalizedPushoutFunctor_changeWeak
  CategoryTheory.Waldhausen.Additivity.normalizedMixedGrid_changeWeak
  CategoryTheory.Waldhausen.Additivity.normalizedMixedMap_changeWeak
