/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialPushout
import Colib.CategoryTheory.Limits.UnderCoproductPushout
import Colib.Topology.Realization.CoproductWeakEquivalence
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Pointed coproducts of stalkwise trivial monomorphisms

The underlying coproduct map is a pushout of the coproduct of the original
underlying maps. A site fiber preserves the unpointed coproducts and the
pushout, giving the pointed coproduct closure.

This is condition E6 of Goerss and Jardine, *Localization theories for
simplicial presheaves*, §1, p. 1050. https://doi.org/10.4153/CJM-1998-051-1
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C)

omit [LocallySmall C] in
private theorem isRealizationWeakEquivalence_presheafFiber_sigmaMap
    (Φ : J.Point.{w}) {ι : Type w} {A B : ι → Cᵒᵖ ⥤ SSet.{w}}
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, SSet.IsRealizationWeakEquivalence ((Φ.presheafFiber (A := SSet.{w})).map (f i))) :
    SSet.IsRealizationWeakEquivalence
      ((Φ.presheafFiber (A := SSet.{w})).map (Limits.Sigma.map f)) := by
  let E := Φ.presheafFiber (A := SSet.{w})
  let g (i : ι) := E.map (f i)
  let eA := (PreservesCoproduct.iso E A)
  let eB := (PreservesCoproduct.iso E B)
  have h (X : ι → Cᵒᵖ ⥤ SSet.{w}) (i : ι) :
      E.map (Limits.Sigma.ι X i) ≫ (PreservesCoproduct.iso E X).hom =
        Limits.Sigma.ι (fun j => E.obj (X j)) i := by
    let e := PreservesCoproduct.iso E X
    apply (cancel_mono e.inv).1
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    exact (ι_comp_sigmaComparison E X i).symm
  apply SSet.IsRealizationWeakEquivalence.of_iso_square _ (Limits.Sigma.map g) eA eB
  · apply (isColimitOfHasCoproductOfPreservesColimit E A).hom_ext
    rintro ⟨i⟩
    change E.map (Limits.Sigma.ι A i) ≫ E.map (Limits.Sigma.map f) ≫ eB.hom =
      E.map (Limits.Sigma.ι A i) ≫ eA.hom ≫ Limits.Sigma.map g
    rw [← Category.assoc, ← E.map_comp, Limits.Sigma.ι_map, E.map_comp,
      Category.assoc, h B i, ← Category.assoc, h A i, Limits.Sigma.ι_map]
  · exact SSet.IsRealizationWeakEquivalence.sigmaMap g hf

/-- The original pointed coproduct of stalkwise trivial monomorphisms is stalkwise trivial. -/
theorem stalkwiseTrivialMonomorphisms_sigmaMap {ι : Type w}
    {X Y : ι → PointedSimplicialPresheaf.{w} C} [HasCoproduct X] [HasCoproduct Y]
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, stalkwiseTrivialMonomorphisms C J (f i)) :
    stalkwiseTrivialMonomorphisms C J (Limits.Sigma.map f) := by
  let g (i : ι) := (f i).right
  let : ∀ i, Mono (g i) := fun i => by
    let : Mono (f i) := (hf i).1
    exact Under.mono_right_of_mono (f i)
  let : Mono (Limits.Sigma.map g) := inferInstance
  have sq : IsPushout (Limits.Sigma.map g) (Under.coproductRightMap X)
      (Under.coproductRightMap Y) (Limits.Sigma.map f).right := Under.sigmaMap_right_isPushout f
  have hm : Mono (Limits.Sigma.map f).right := by
    let W := monomorphisms (Cᵒᵖ ⥤ SSet.{w})
    let : W.IsStableUnderCobaseChange := by
      change (monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderCobaseChange
      rw [← functorCategory_monomorphisms]
      infer_instance
    exact W.of_isPushout sq.flip (inferInstanceAs (Mono (Limits.Sigma.map g)))
  let : Mono (Limits.Sigma.map f).right := hm
  refine ⟨Under.mono_of_mono_right _, fun Φ => ?_⟩
  exact isRealizationWeakEquivalence_presheafFiber_of_isPushout C J Φ sq
    (isRealizationWeakEquivalence_presheafFiber_sigmaMap C J Φ g (fun i => (hf i).2 Φ))

instance stalkwiseTrivialMonomorphisms_isStableUnderCoproducts :
    (stalkwiseTrivialMonomorphisms.{w} C J).IsStableUnderCoproducts.{w} where
  isStableUnderCoproductsOfShape ι := by
    let W := stalkwiseTrivialMonomorphisms.{w} C J
    let : W.RespectsIso := respectsIso_of_isStableUnderComposition
      (fun (X Y : PointedSimplicialPresheaf.{w} C) (f : X ⟶ Y) hf => by
        let : IsIso f := hf
        let e := @asIso _ _ _ _ f hf
        exact ⟨mono_of_mono_fac e.hom_inv_id, fun Φ =>
          let : IsIso ((fiberAtPoint C Φ).map f) := (fiberAtPoint C Φ).map_isIso f
          SSet.realizationWeakEquivalences_of_isIso _⟩)
    exact IsStableUnderCoproductsOfShape.mk W ι (fun _ _ _ _ f hf =>
      stalkwiseTrivialMonomorphisms_sigmaMap C J f hf)

end CategoryTheory.PointedSimplicialPresheaf
