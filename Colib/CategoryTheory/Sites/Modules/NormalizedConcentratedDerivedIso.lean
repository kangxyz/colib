/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.ConcentratedDerivedIso

/-!
# Homology-normalized internal truncation

Crucially choose ONLY the intermediate single object and
iso. Construct the normalization explicitly outside Classical.choice so its H0
property is provable and not lost by existential proof irrelevance.
-/

@[expose] public noncomputable section
open CategoryTheory
universe w v u
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Internal concentrated reconstruction normalized on actual homology. -/
def normalizedConcentratedHomologyIso (X : DerivedCategory C) (n : ℤ)
    [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X) :=
  let h := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose h
  let e : X ≅ (singleFunctor C n).obj Y := Classical.choice (Classical.choose_spec h)
  let eH : (homologyFunctor C n).obj X ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C n).app Y
  e ≪≫ (singleFunctor C n).mapIso eH.symm

/-- The normalization is the identity on homology under the native single comparison. -/
theorem normalizedConcentratedHomologyIso_homology (X : DerivedCategory C) (n : ℤ)
    [X.IsGE n] [X.IsLE n] :
    (homologyFunctor C n).map (normalizedConcentratedHomologyIso X n).hom ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app
        ((homologyFunctor C n).obj X) = 𝟙 _ := by
  let h := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose h
  let e : X ≅ (singleFunctor C n).obj Y := Classical.choice (Classical.choose_spec h)
  let eH : (homologyFunctor C n).obj X ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C n).app Y
  change (homologyFunctor C n).map (e.hom ≫ (singleFunctor C n).map eH.inv) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  have hc := (singleFunctorCompHomologyFunctorIso C n).hom.naturality eH.inv
  change (homologyFunctor C n).map ((singleFunctor C n).map eH.inv) ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app _ =
    (singleFunctorCompHomologyFunctorIso C n).hom.app Y ≫ eH.inv at hc
  rw [hc, ← Category.assoc]
  exact eH.hom_inv_id

end DerivedCategory
