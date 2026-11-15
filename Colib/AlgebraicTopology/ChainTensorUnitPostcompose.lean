/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ChainTensorUnitNaturality
/-! # Native coordinate transport with its actual target map -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- Both coordinate factors transport through the native tensor and a specified
actual target morphism; no structure map is replaced or assumed invertible. -/
theorem chainUnitCoordinate_fullTransport_postcompose
    {K L L' M M' Z : ChainComplex C ℕ} (a : K ⟶ L)
    (b : HomologicalComplex.tensorUnit C (.down ℕ) ⟶ M)
    (e : L ⟶ L') (f : M ⟶ M') (c : HomologicalComplex.tensorObj L' M' ⟶ Z) :
    (a ≫ ((HomologicalComplex.rightUnitor L).inv ≫
      HomologicalComplex.tensorHom (𝟙 L) b)) ≫
      (HomologicalComplex.tensorHom e f ≫ c) =
    ((HomologicalComplex.rightUnitor K).inv ≫
      HomologicalComplex.tensorHom (a ≫ e) (b ≫ f)) ≫ c :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun x => x ≫ c) (chainUnitCoordinate_fullTransport a b e f))

end AlgebraicTopology
