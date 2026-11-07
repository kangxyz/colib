/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.BisimplexFamily
public import Colib.Topology.Realization.ProductSimplex
public import Colib.KTheory.Waldhausen.Map

/-! # Realizing the two independent coordinates of an original quotient grid

An actual certified bisimplex gives a map from the product of its two standard simplices
into the original diagonal S-construction. The continuous family retains both barycentric
coordinates and their exact reindexing, rather than choosing a homotopy witness.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/SConstruction/BisimplexRealization.lean`,
lines 40–81, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
open CategoryTheory Opposite MonoidalCategory Convexity
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)

/-- The original grid realized with independent barycentric S and nerve coordinates. -/
def bisimplexRealization :
    C(StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)), |sSet W.cof W.weq|) :=
  (SSet.toTop.map (bisimplexFamily W F hF)).hom.comp
    ⟨(realizationProductSimplexHomeomorph n m).symm,
      (realizationProductSimplexHomeomorph n m).symm.continuous⟩

/-- The specified continuous family keeps the actual inverse product-simplex comparison. -/
theorem bisimplexRealization_apply
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    bisimplexRealization W F hF (z, t) =
      SSet.toTop.map (bisimplexFamily W F hF)
        ((realizationProductSimplexHomeomorph n m).symm (z, t)) := rfl

/-- The entire continuous family commutes with both original simplex operators. -/
theorem bisimplexRealization_precomp {n' m' : ℕ}
    (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌)
    (z : StdSimplex ℝ (Fin (n' + 1))) (t : StdSimplex ℝ (Fin (m' + 1))) :
    bisimplexRealization W F hF (z.map α, t.map β) =
      bisimplexRealization W (gridMap₂ α β ⋙ F)
        (hF.precomp W.cof W.weq α β) (z, t) := by
  have hx :
      SSet.toTop.map (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β)
          ((realizationProductSimplexHomeomorph n' m').symm (z, t)) =
        (realizationProductSimplexHomeomorph n m).symm (z.map α, t.map β) := by
    apply (realizationProductSimplexHomeomorph n m).injective
    rw [Homeomorph.apply_symm_apply, realizationProductSimplexHomeomorph_naturality,
      Homeomorph.apply_symm_apply]
  change SSet.toTop.map (bisimplexFamily W F hF)
      ((realizationProductSimplexHomeomorph n m).symm (z.map α, t.map β)) = _
  rw [← hx]
  change (SSet.toTop.map (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β) ≫
    SSet.toTop.map (bisimplexFamily W F hF)) _ = _
  rw [← Functor.map_comp, bisimplexFamily_precomp]
  rfl

/-- Equal original grids give equal specified continuous realization families. -/
theorem bisimplexRealization_congr {G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C}
    (hG : IsSimplex₂ W.cof W.weq G) (h : F = G) :
    bisimplexRealization W F hF = bisimplexRealization W G hG := by
  cases h
  rfl

end CategoryTheory.Waldhausen

/-!
## Additional implementation provenance

Adapted from `Quillen/Waldhausen/AutomorphismKOne.lean`, lines 142–151,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original declarations, full coordinates, hypotheses and universes are retained.
Only native namespaces, precise imports and line wrapping change. Source-only, UNCOMPILED.
-/
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Both independent simplex coordinates are retained by the original exact realization map. -/
theorem bisimplexRealization_postcompose {n m : ℕ}
    (G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hG : IsSimplex₂ V.cof V.weq G)
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    deloopingMap hF (bisimplexRealization V G hG (z, t)) =
      bisimplexRealization W (G ⋙ F) (hG.postcomp V.cof V.weq hF) (z, t) := by
  change (SSet.toTop.map (bisimplexFamily V G hG) ≫
    SSet.toTop.map (sSetMap hF)) ((realizationProductSimplexHomeomorph n m).symm (z, t)) = _
  rw [← Functor.map_comp, bisimplexFamily_postcompose]
  rfl

end CategoryTheory.Waldhausen
