/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal


/-! # Independent simplicial families of an original quotient grid

The actual certified grid gives a map from the product of its two standard simplices
into the original diagonal S-construction. Both simplex operators remain independent,
with equality of the entire original grid, including mixed maps. -/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/SConstruction/BisimplexRealization.lean`
   at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
   Original objects, maps, hypotheses and universe parameters are retained.
   Source-only preparation; native validation remains pending. -/
@[expose] public section
noncomputable section
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)

/-- Reindex the actual quotient grid independently along the two original simplex arrows. -/
def bisimplexFamily : (Δ[n] ⊗ Δ[m] : SSet.{max u v}) ⟶ sSet W.cof W.weq where
  app k := ↾fun z ↦ ⟨gridMap₂ z.1.down z.2.down ⋙ F,
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp
      (hF.precomp W.cof W.weq z.1.down z.2.down)⟩
  naturality _ _ _ := by ext z; rfl

/-- Both standard-simplex operators retain the entire original grid under reindexing. -/
theorem bisimplexFamily_precomp {n' m' : ℕ} (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌) :
    (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β) ≫ bisimplexFamily W F hF =
      bisimplexFamily W (gridMap₂ α β ⋙ F) (hF.precomp W.cof W.weq α β) := by
  ext k z
  rfl

end CategoryTheory.Waldhausen
