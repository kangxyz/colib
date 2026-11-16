module

public import Colib.KTheory.Waldhausen.Iterated.SimplexFamily

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial

universe u

namespace ColibTest.IteratedSimplexFamily

variable {V W : WideSubcategory preservesZero.{u}}

/-- The next genuine stage uses the same full three-dimensional chain on its quotient row. -/
theorem successor_cube (r : ℕ) (S : ModelSimplex V W 3) (n : SimplexCategoryᵒᵖ)
    (A : ((stages (r + 1)).obj V).obj n) (τ : (Δ[3]).obj n) :
    stageSimplexFunction (r + 1) S n A τ =
      stageSimplexFunction r (S.rows n.unop) n A τ := rfl

/-- The prescribed cube face retains the actual subchain, not merely its endpoint maps. -/
theorem cube_face (r : ℕ) (S : ModelSimplex V W 3) (α : ⦋2⦌ ⟶ ⦋3⦌)
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[2]).obj n) :
    stageSimplexFunction r S n A ⟨τ.down ≫ α⟩ =
      stageSimplexFunction r (S.face α) n A τ :=
  stageSimplexFunction_face r S α n A τ

/-- At every original degree the entire finite parameter fixes the original zero. -/
theorem cube_zero (r : ℕ) (S : ModelSimplex V W 3) (n : SimplexCategoryᵒᵖ)
    (τ : (Δ[3]).obj n) :
    stageSimplexFunction r S n (stageZeroSimplex r V n) τ = stageZeroSimplex r W n :=
  stageSimplexFunction_zeroSimplex r S n τ

end ColibTest.IteratedSimplexFamily
