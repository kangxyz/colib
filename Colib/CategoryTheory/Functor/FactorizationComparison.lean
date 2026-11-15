/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Functor.IsoRouteConjugation

/-! # Comparing functors through a pair of factorization squares -/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

/-- Compare two composites through two pasted factorization squares and the specified maps
at their ends. -/
def factorizationComparison
    {J H D E : Type*} [Category* J] [Category* H] [Category* D] [Category* E]
    {U₀ U₁ : J ⥤ J} {U₂ F₀ : H ⥤ H} {V₀ L : J ⥤ D}
    {V : D ⥤ E} {Q : H ⥤ E} {I : J ⥤ H}
    (d : V₀ ⋙ V ≅ I ⋙ Q) (e : U₁ ⋙ I ≅ I ⋙ U₂) (c : L ⋙ V ≅ I ⋙ F₀ ⋙ Q)
    (η : U₀ ⟶ U₁) (θ : U₂ ⟶ F₀) : (U₀ ⋙ V₀) ⋙ V ⟶ L ⋙ V :=
  whiskerRight (whiskerRight η V₀) V ≫ (isoSquareRoute e d).hom ≫
    whiskerLeft I (whiskerRight θ Q) ≫ c.inv

/-- The component of the comparison is the composite of the two boundary maps and the
three factorization components. -/
theorem factorizationComparison_app
    {J H D E : Type*} [Category* J] [Category* H] [Category* D] [Category* E]
    {U₀ U₁ : J ⥤ J} {U₂ F₀ : H ⥤ H} {V₀ L : J ⥤ D}
    {V : D ⥤ E} {Q : H ⥤ E} {I : J ⥤ H}
    (d : V₀ ⋙ V ≅ I ⋙ Q) (e : U₁ ⋙ I ≅ I ⋙ U₂) (c : L ⋙ V ≅ I ⋙ F₀ ⋙ Q)
    (η : U₀ ⟶ U₁) (θ : U₂ ⟶ F₀) (K : J) :
    (factorizationComparison d e c η θ).app K =
      V.map (V₀.map (η.app K)) ≫ d.hom.app (U₁.obj K) ≫ Q.map (e.hom.app K) ≫
        Q.map (θ.app (I.obj K)) ≫ c.inv.app K := by
  simp only [factorizationComparison, isoSquareRoute, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.assoc]

end CategoryTheory.Functor
