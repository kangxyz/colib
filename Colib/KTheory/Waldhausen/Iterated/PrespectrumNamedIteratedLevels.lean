/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedTransformationLevels
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy

/-!
# Named native iterated levels with their actual source and association transports

Source equality is eliminated only with abstract native arrows. Right whiskering
uses the original association-aware wrapper and the two native associativity
certificates. Every statement compares the complete continuous level map.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- Precomposition is the entire level of the named source-transported left whisker.
The source equality is an honest native-arrow equality, not a level profile. -/
theorem prespectrumModelWhiskerLeftSourceHomotopy_level_of_eq
    {U V W : WideSubcategory preservesZero.{u}}
    (A : U ⟶ V) {P Q : V ⟶ W} {F : U ⟶ W} (eF : F = A ≫ P)
    (μ : P.hom.toFunctor ⟶ Q.hom.toFunctor)
    (hμ : ∀ X, W.obj.waldhausen.weq (μ.app X))
    (β : F.hom.toFunctor ⟶ (A ≫ Q).hom.toFunctor)
    (hβ : ∀ X, W.obj.waldhausen.weq (β.app X))
    (eβ : β = modelEqToHom eF ≫ modelWhiskerLeft A μ) (n : ℕ) :
    (Homotopy.precomp (prespectrumMap A)
      (prespectrumTransformationHomotopy (F := P) (G := Q) μ hμ)).level n =
        (prespectrumTransformationHomotopy (F := F) (G := A ≫ Q) β hβ).level n := by
  subst F
  apply prespectrumModelWhiskerLeftHomotopy_level_of_eq A μ hμ β hβ _ n
  simpa only [modelEqToHom_eq, eqToHom_refl, Category.id_comp] using eβ

/-- The entire postcomposed level is the named association-aware right whisker.
Both native associativity witnesses are retained before comparison of levels. -/
theorem prespectrumModelWhiskerRightAssocHomotopy_level_of_eq
    {U V W X Y : WideSubcategory preservesZero.{u}}
    (A : U ⟶ V) (E : V ⟶ W) (B : U ⟶ X) (P : X ⟶ W) (Q : W ⟶ Y)
    (α : (A ≫ E).hom.toFunctor ⟶ (B ≫ P).hom.toFunctor)
    (hα : ∀ Z, W.obj.waldhausen.weq (α.app Z))
    (γ : (A ≫ (E ≫ Q)).hom.toFunctor ⟶ (B ≫ (P ≫ Q)).hom.toFunctor)
    (hγ : ∀ Z, Y.obj.waldhausen.weq (γ.app Z))
    (eγ : γ = modelWhiskerRightAssoc A E B P Q α) (n : ℕ) :
    ((prespectrumTransformationHomotopy
      (F := A ≫ E) (G := B ≫ P) α hα).postcomp (prespectrumMap Q)).level n =
        (prespectrumTransformationHomotopy
          (F := A ≫ (E ≫ Q)) (G := B ≫ (P ≫ Q)) γ hγ).level n := by
  exact (prespectrumTransformationHomotopy_postcomp_level
    (F := A ≫ E) (G := B ≫ P) α hα Q n).symm.trans
      (prespectrumTransformationHomotopy_congr_level
        (F := (A ≫ E) ≫ Q) (G := (B ≫ P) ≫ Q)
        (F' := A ≫ (E ≫ Q)) (G' := B ≫ (P ≫ Q))
        (Category.assoc A E Q) (Category.assoc B P Q)
        (whiskerRight α Q.hom.toFunctor) γ
        (fun Z => Q.hom.isExact.weak _ (hα Z)) hγ
        (by
          simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
            ((modelWhiskerRightAssoc_eq A E B P Q α).symm.trans eγ.symm)) n)

end CategoryTheory.Waldhausen.IteratedS
