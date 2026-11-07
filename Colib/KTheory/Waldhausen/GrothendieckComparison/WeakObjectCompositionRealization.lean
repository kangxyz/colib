/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakObjectCompositionPrism
public import Colib.KTheory.Waldhausen.Basic
public import Colib.KTheory.Waldhausen.BisimplexRealization
public import Colib.Topology.Realization.Constant

/-!
# The actual first face and constant vertex triangles of a weak-composition prism

Realize the original two-arrow grid using independent object-edge and nerve-triangle
coordinates. The first continuous face and the entire constant vertex triangles supply
the endpoint laws needed for the prescribed weak-object square.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionPrism.lean`,
lines 77–107, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Also `GrothendieckComparison/WeakObjectCompositionBased.lean`, lines 47–75.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Convexity
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- The actual independent object-edge and nerve-triangle coordinates. -/
def weakObjectCompositionRealization :
    C(StdSimplex ℝ (Fin 2) × StdSimplex ℝ (Fin 3), W.Delooping) :=
  bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg)

/-- The whole product-simplex realization retains both original coordinates. -/
theorem weakObjectCompositionRealization_apply
    (t : StdSimplex ℝ (Fin 2)) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (t, z) =
      bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
        (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (t, z) := rfl

/-- The first continuous face is the entire original weak-arrow square. -/
theorem weakObjectCompositionRealization_first
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 2)) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex f hf).property) (t, z) := by
  have h := bisimplexRealization_precomp W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (𝟙 ⦋1⦌) (SimplexCategory.δ 2) t z
  have he := bisimplexRealization_congr W _
    ((W.weakObjectCompositionPrism_isSimplex₂ f g hf hg).precomp W.cof W.weq
      (𝟙 ⦋1⦌) (SimplexCategory.δ 2))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex f hf).property)
    (W.weakObjectCompositionPrism_first f g hf hg)
  rw [he] at h
  rw [weakObjectCompositionRealization_apply]
  simpa using h

/-- The whole nerve triangle stays at the literal basepoint on either object-edge endpoint. -/
theorem weakObjectCompositionRealization_vertex (e : Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (StdSimplex.single e, z) = W.kBasepoint := by
  have he : bisimplexFamily W
      (gridMap₂ (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌) ⋙
        W.weakObjectCompositionPrism f g hf hg)
      ((W.weakObjectCompositionPrism_isSimplex₂ f g hf hg).precomp W.cof W.weq
        (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌)) =
        SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
    rw [← bisimplexFamily_precomp]
    simpa using W.weakObjectCompositionFamily_vertex f g hf hg e
  have h := bisimplexRealization_precomp W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg)
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌) (StdSimplex.single 0) z
  rw [bisimplexRealization_apply W
    (gridMap₂ (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌) ⋙
      W.weakObjectCompositionPrism f g hf hg), he, realization_const_apply] at h
  have hc : (ConcreteCategory.hom (SimplexCategory.const ⦋0⦌ ⦋1⦌ e)) 0 = e := rfl
  have hi : (⇑(ConcreteCategory.hom (𝟙 ⦋2⦌)) : Fin 3 → Fin 3) = id := rfl
  have hb : realizationPoint (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) =
      W.kBasepoint := by
    unfold realizationPoint kBasepoint basepoint
    exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)))) (Subsingleton.elim _ _)
  rw [hb] at h
  change bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (StdSimplex.single e, z) =
      (W.kBasepoint : |sSet W.cof W.weq|)
  simpa only [StdSimplex.map_single, hc, hi, StdSimplex.map_id] using h

end CategoryTheory.Waldhausen.Structure
