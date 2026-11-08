/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.PostcomposeDetection

/-!
# Heterogeneous detection of extension cofibrations

Lifts joint detection of cofibrations by exact functors to the Reedy cofibration
class on extension categories. The family and pair forms retain the original
detection hypotheses, with the pair form allowing two different target categories.

Implementation provenance: `Quillen/Waldhausen/ExtensionCategory/HeterogeneousDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original hypotheses, functors, component maps and independent universes are retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v'' w
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (V : Structure C)
/-- Actual cofibration detection by different target categories lifts to the genuine Reedy class. -/
theorem cof_of_postcompose_heterogeneous {ι : Sort w} (D : ι → Type u')
    [∀ i, Category.{v'} (D i)] (W : ∀ i, Structure (D i)) (F : ∀ i, C ⥤ D i)
    (hF : ∀ i, IsExact V.cof V.weq (W i).cof (W i).weq (F i))
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), (∀ i, (W i).cof ((F i).map f)) → V.cof f)
    {X Y : Obj V} {f : X ⟶ Y}
    (hf : ∀ i, cof (W i) ((postcompose V (W i) (hF i)).map f)) : cof V f :=
  ⟨detect _ (fun i => (hf i).1),
    detect _ (fun i => mapped_relative_cof V (W i) (hF i) (hf i))⟩
/-- Two exact projections into genuinely different categories jointly detect
relative cofibrations whenever they detect the original cofibration class. -/
@[colib_tag "COL-0310",
  colib_ref "quillen" "Quillen/Waldhausen/ExtensionCategory/HeterogeneousDetection.lean:35-45"
    "adaptation" "Detection of genuine relative cofibrations by two different exact targets"]
theorem cof_of_postcompose_pair {D : Type u'} [Category.{v'} D]
    {E : Type u''} [Category.{v''} E] (W : Structure D) (U : Structure E)
    {F : C ⥤ D} {G : C ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), W.cof (F.map f) → U.cof (G.map f) → V.cof f)
    {X Y : Obj V} {f : X ⟶ Y}
    (hf : cof W ((postcompose V W hF).map f))
    (hg : cof U ((postcompose V U hG).map f)) : cof V f :=
  ⟨detect _ hf.1 hg.1,
    detect _ (mapped_relative_cof V W hF hf) (mapped_relative_cof V U hG hg)⟩
end CategoryTheory.Waldhausen.ExtensionCategory
