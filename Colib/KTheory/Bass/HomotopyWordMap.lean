/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.KTheory.Bass.HomotopyWordNaturality

/-!
# Bass preserves the original whole homotopy words

The literal natural time slices show preservation of reversal and the original
half-clock concatenation. These finite formulas are used for the original
source-null/unit/source-null word, without adding a coherence hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.HomotopyWord
variable {C : Type u} [Category.{v} C]
  {F G : C ⥤ LoopPrespectrum.{w}} {a b c : F ⟶ G}

/-- Bass preserves reversal of the entire natural homotopy, including all structure values. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/HomotopyWord.lean:60"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem map_symm (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H)
    (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    strictDiagramMapHomotopy (fun Y => (H Y).symm) (natural_symm H hH) Q X =
      (strictDiagramMapHomotopy H hH Q X).symm := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  change ((strictDiagramMapHomotopy _ _ Q X).at r).map n x =
    ((strictDiagramMapHomotopy H hH Q X).at (unitInterval.symm r)).map n x
  rw [strictDiagramMapHomotopy_at, strictDiagramMapHomotopy_at]
  rfl

/-- Bass preserves the original half-clock concatenation literally. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/HomotopyWord.lean:74"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem map_trans (H : ∀ X, Homotopy (a.app X) (b.app X))
    (K : ∀ X, Homotopy (b.app X) (c.app X)) (hH : Natural H) (hK : Natural K)
    (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    strictDiagramMapHomotopy (fun Y => (H Y).trans (K Y))
        (natural_trans H K hH hK) Q X =
      (strictDiagramMapHomotopy H hH Q X).trans (strictDiagramMapHomotopy K hK Q X) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  change ((strictDiagramMapHomotopy _ _ Q X).at r).map n x =
    ((strictDiagramMapHomotopy H hH Q X).levelHomotopy n).trans
      ((strictDiagramMapHomotopy K hK Q X).levelHomotopy n) (r,x)
  rw [strictDiagramMapHomotopy_at, ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i hr
    change _ = ((strictDiagramMapHomotopy H hH Q X).at _).map n x
    rw [strictDiagramMapHomotopy_at]
    apply congrArg (fun η => (((strictDiagramFunctor Q).map η).app X).map n x)
    apply NatTrans.ext
    funext Y
    apply Hom.ext
    funext m
    apply ContinuousMap.ext
    intro y
    change ((H Y).levelHomotopy m).trans ((K Y).levelHomotopy m) (r,y) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    simp only [hr, dite_true]
    rfl
  · rename_i hr
    change _ = ((strictDiagramMapHomotopy K hK Q X).at _).map n x
    rw [strictDiagramMapHomotopy_at]
    apply congrArg (fun η => (((strictDiagramFunctor Q).map η).app X).map n x)
    apply NatTrans.ext
    funext Y
    apply Hom.ext
    funext m
    apply ContinuousMap.ext
    intro y
    change ((H Y).levelHomotopy m).trans ((K Y).levelHomotopy m) (r,y) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    simp only [hr, dite_false]
    rfl

/-- Original postcomposition becomes Bass postcomposition at every identical time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/HomotopyWord.lean:119"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem map_postcomp {D : C ⥤ LoopPrespectrum.{w}}
    (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) (j : G ⟶ D)
    (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ) :
    (strictDiagramMapHomotopy (η := a ≫ j) (θ := b ≫ j)
      (fun Y => (H Y).postcomp (j.app Y))
      (natural_postcomp H hH j) Q X).level n =
    ((strictDiagramMapHomotopy H hH Q X).postcomp
      (((strictDiagramFunctor Q).map j).app X)).level n := by
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  change ((strictDiagramMapHomotopy _ _ Q X).at r).map n x =
    ((strictDiagramMapHomotopy H hH Q X).at r ≫
      (((strictDiagramFunctor Q).map j).app X)).map n x
  rw [strictDiagramMapHomotopy_at, strictDiagramMapHomotopy_at]
  exact congrArg (fun k => (k.app X).map n x)
    ((strictDiagramFunctor Q).map_comp (diagramHomotopyAt H hH r) j)

end KTheory.Bass.HomotopyWord
