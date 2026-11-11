/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparisonIso
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# The actual small-model composition comparison and its original track

The transported lift of an original composition isomorphism gives the same complete
prespectrum track as the original-universe transformation constructor. The two actual
model endpoint projections and both spectrum endpoint casts remain explicit.
The equality uses the existing whole-track congruence and natural-transformation
transport formulas, without projecting components in a concrete category.
-/
@[expose] public noncomputable section

open CategoryTheory Topology.LoopPrespectrum

universe u v

namespace CategoryTheory.Waldhausen.IteratedS

private theorem transportIso_hom_comp_eqToHom
    {A B : Type*} [Category* A] [Category* B] {F F' G G' : A ⥤ B}
    (hF : F = F') (hG : G = G') (i : F' ≅ G') :
    (Functor.transportIso hF hG i).hom ≫ eqToHom hG = eqToHom hF ≫ i.hom := by
  cases hF
  cases hG
  change (𝟙 F ≫ i.hom ≫ 𝟙 G) ≫ 𝟙 G = 𝟙 F ≫ i.hom
  simp only [Category.id_comp, Category.comp_id]

/-- The lifted actual composition iso retains the whole original transformation track,
including the two specified model projections and the canonical target-arrow casts. -/
theorem modelAsSmallCompositionIso_prespectrumHomotopy_level
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (W : Structure C) (V : Structure D) (U : Structure E)
    {H : C ⥤ E} {F : C ⥤ D} {G : D ⥤ E}
    (hH : IsExact W.cof W.weq U.cof U.weq H)
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (h0H : H.obj W.zero = U.zero) (h0F : F.obj W.zero = V.zero)
    (h0G : G.obj V.zero = U.zero) (i : H ≅ F ⋙ G)
    (hSource : (asSmallCategoryMap W U hH h0H).hom.toFunctor = asSmallFunctor H)
    (hTarget : (asSmallCategoryMap W V hF h0F ≫
      asSmallCategoryMap V U hG h0G).hom.toFunctor =
        asSmallFunctor F ⋙ asSmallFunctor G) (n : ℕ) :
    ((prespectrumTransformationHomotopy
      (F := asSmallCategoryMap W U hH h0H)
      (G := asSmallCategoryMap W V hF h0F ≫ asSmallCategoryMap V U hG h0G)
      (modelAsSmallCompositionIso W U F G H i hSource hTarget).hom
      (fun x ↦ U.asSmall.weq_iso _ (by
        change IsIso ((modelAsSmallCompositionIso W U F G H i hSource hTarget).hom.app x)
        infer_instance))).cast rfl (prespectrumFunctor.map_comp _ _)).level n =
      ((originalPrespectrumTransformationHomotopy W U hH (hF.comp hG)
        h0H ((congrArg G.obj h0F).trans h0G) i.hom
        (fun _ ↦ U.weq_iso _ inferInstance)).cast rfl
        (originalPrespectrumMap_comp W V U hF hG h0F h0G)).level n := by
  simp only [originalPrespectrumTransformationHomotopy]
  apply prespectrumTransformationHomotopy_congr_level rfl
    (asSmallCategoryMap_comp W V U hF hG h0F h0G).symm
  change (Functor.transportIso hSource hTarget (asSmallCompositionIso F G H i)).hom ≫
      eqToHom hTarget = eqToHom hSource ≫ (asSmallCompositionIso F G H i).hom
  exact transportIso_hom_comp_eqToHom hSource hTarget (asSmallCompositionIso F G H i)

end CategoryTheory.Waldhausen.IteratedS
