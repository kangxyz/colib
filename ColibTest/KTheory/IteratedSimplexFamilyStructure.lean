module

public import Colib.KTheory.Waldhausen.Iterated.SimplexFamilyStructure

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial

universe u

namespace ColibTest.IteratedSimplexFamilyStructure

variable {V W : WideSubcategory preservesZero.{u}}

/-- The actual three-dimensional parameter is independent of original suspension. -/
theorem cube_suspension (r : ℕ) (S : ModelSimplex V W 3) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) (θ : (Δ[3]).obj n) :
    stageSimplexFunction (r + 1) S n ((stageCylinder r V).app n (A, τ)) θ =
      (stageCylinder r W).app n (stageSimplexFunction r S n A θ, τ) :=
  stageSimplexFunction_structure r S n A τ θ

end ColibTest.IteratedSimplexFamilyStructure
