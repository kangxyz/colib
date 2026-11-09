/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalization
public import Colib.CategoryTheory.Functor.Rebase
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Canonical chosen-zero normalization of section coefficients

The normalization is the actual rebasing natural isomorphism formed from uniqueness
of zero objects. The composition and unit constraints are derived from the original
pseudofunctor constraints, not supplied independently.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
  (z : ∀ R : C, F.obj ⟨R⟩) (hz : ∀ R, IsZero (z R))
  (hm : ∀ {R S : C} (f : R ⟶ S), IsZero ((F.map f.toLoc).toFunctor.obj (z R)))

/-- The coefficient functor rebased using the canonical isomorphism of its zero objects. -/
def zeroNormalizedFunctor {R S : C} (f : R ⟶ S) : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩ :=
  rebaseFunctor (F.map f.toLoc).toFunctor (z R) (z S) ((hm f).iso (hz S))

/-- The unchanged rebasing comparison for the actual coefficient functor. -/
def zeroNormalizationIso {R S : C} (f : R ⟶ S) :
    (F.map f.toLoc).toFunctor ≅ zeroNormalizedFunctor F z hz hm f :=
  rebaseFunctorIso (F.map f.toLoc).toFunctor (z R) (z S) ((hm f).iso (hz S))

/-- Normalized coefficients preserve the specified zeros by equality. -/
theorem zeroNormalizedFunctor_obj_zero {R S : C} (f : R ⟶ S) :
    (zeroNormalizedFunctor F z hz hm f).obj (z R) = z S :=
  rebaseFunctor_obj_base _ _ _ _

/-- The actual zero-normalized comparison, not a separately chosen evaluation equivalence. -/
def zeroNormalizedCoefficientIso {R S : C} (f : R ⟶ S) :=
  normalizedCoefficientIso F f (zeroNormalizationIso F z hz hm f)

/-- The actual zero-normalized composition constraint. -/
def zeroNormalizedCoefficientCompIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :=
  normalizedCoefficientCompIso F f g (zeroNormalizationIso F z hz hm f)
    (zeroNormalizationIso F z hz hm g) (zeroNormalizationIso F z hz hm (f ≫ g))

/-- The actual zero-normalized unit constraint. -/
def zeroNormalizedCoefficientIdIso (R : C) :=
  normalizedCoefficientIdIso F R (zeroNormalizationIso F z hz hm (𝟙 R))

/-- The canonical forward comparison still starts with the actual section evaluation. -/
theorem zeroNormalizedCoefficientIso_hom {R S : C} (f : R ⟶ S) :
    (zeroNormalizedCoefficientIso F z hz hm f).hom =
      (originalCoefficientIso F f).hom ≫
        whiskerLeft (originalEvaluation F R) (zeroNormalizationIso F z hz hm f).hom := rfl

/-- Canonical zero normalization satisfies the complete forward two-arrow equation. -/
@[colib_tag "COL-0356"]
theorem zeroNormalizedCoefficientIso_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (zeroNormalizedCoefficientIso F z hz hm (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation F R) (zeroNormalizedCoefficientCompIso F z hz hm f g).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (normalizedCoefficientRouteIso F f g (zeroNormalizationIso F z hz hm f)
            (zeroNormalizationIso F z hz hm g)).hom :=
  normalizedCoefficientIso_comp_hom F f g _ _ _

/-- Canonical zero normalization satisfies the forward identity equation with its actual unit. -/
@[colib_tag "COL-0356"]
theorem zeroNormalizedCoefficientIso_id_hom (R : C) :
    (zeroNormalizedCoefficientIso F z hz hm (𝟙 R)).hom ≫
        whiskerLeft (originalEvaluation F R) (zeroNormalizedCoefficientIdIso F z hz hm R).hom ≫
        (Functor.rightUnitor (originalEvaluation F R)).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
        (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R)) ≫
          (Functor.leftUnitor (originalEvaluation F R)).hom :=
  normalizedCoefficientIso_id_hom F R _

end CategoryTheory.GrothendieckSections
