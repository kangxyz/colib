/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialPushout
import Colib.Topology.FilteredRealization.TransfiniteComposition
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Transfinite compositions of stalkwise trivial monomorphisms

The forgetful functor and the site fibers preserve the original connected
colimits. This transports monomorphisms and realization weak equivalences
through the stages of a well-ordered pointed presheaf construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C)

instance stalkwiseTrivialMonomorphisms_isStableUnderTransfiniteCompositionOfShape
    (I : Type w) [LinearOrder I] [SuccOrder I] [OrderBot I] [WellFoundedLT I] :
    (stalkwiseTrivialMonomorphisms.{w} C J).IsStableUnderTransfiniteCompositionOfShape I where
  le X Y f hf := by
    obtain ⟨t⟩ := hf
    let F := forget.{w} C
    let : PreservesWellOrderContinuousOfShape I F := ⟨fun i hi => by
      let : Nonempty (Set.Iio i) := ⟨⟨⊥, Order.IsSuccLimit.bot_lt hi⟩⟩
      let : IsConnected (Set.Iio i) := IsFiltered.isConnected _
      infer_instance⟩
    let : IsConnected I := IsFiltered.isConnected _
    let W := monomorphisms (Cᵒᵖ ⥤ SSet.{w})
    let : W.IsStableUnderTransfiniteCompositionOfShape I := inferInstanceAs
      ((monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderTransfiniteCompositionOfShape I)
    have tF : (W.inverseImage F).TransfiniteCompositionOfShape I f :=
      t.ofLE (fun _ _ g hg => by
        let : Mono g := hg.1
        exact Under.mono_right_of_mono g)
    have hF : W (F.map f) := W.transfiniteCompositionsOfShape_le I _ ⟨tF.map⟩
    let : Mono f.right := hF
    refine ⟨Under.mono_of_mono_right f, fun Φ => ?_⟩
    let E := fiberAtPoint C Φ
    let : PreservesWellOrderContinuousOfShape I E := ⟨fun i hi => by
      let : Nonempty (Set.Iio i) := ⟨⟨⊥, Order.IsSuccLimit.bot_lt hi⟩⟩
      let : IsConnected (Set.Iio i) := IsFiltered.isConnected _
      unfold E fiberAtPoint
      infer_instance⟩
    let : PreservesColimitsOfShape I E := by
      unfold E fiberAtPoint
      infer_instance
    let P := SSet.realizationWeakEquivalences.{w}
    have tE : (P.inverseImage E).TransfiniteCompositionOfShape I f :=
      t.ofLE (fun _ _ _ hg => hg.2 Φ)
    exact P.transfiniteCompositionsOfShape_le I _ ⟨tE.map⟩

end CategoryTheory.PointedSimplicialPresheaf
