/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationZeroNormalization
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# End-to-end consumers of actual section coefficient coherence

Independent base/fiber universes, arbitrary composable coefficients, equality
transports, actual zero rebasing and canonical forward equations are retained.
The concrete final test has two nonidentity coefficients, rather than testing
only identity arrows. No geometric or spectrum comparison is asserted.
-/
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
universe u v u' v'
namespace ColibTest.SectionTransitionCoherence
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

example {R S : C} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (originalCoefficientIso F f).hom.app s =
      (eqToIso (originalEvaluation_reindex F R f)).hom.app s ≫
        (originalEvaluationTransitionIso F R (Under.mk f)).inv.app s :=
  originalCoefficientIso_hom_app F f s

example {R S : C} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (originalCoefficientIso F f).inv.app s =
      originalTransition F R s (Under.mk f) ≫
        (eqToIso (originalEvaluation_reindex F R f)).inv.app s :=
  originalCoefficientIso_inv_app F f s

example {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (F.map g.toLoc).toFunctor.map ((eqToIso (originalEvaluation_reindex F R f)).inv.app s) ≫
        originalTransition F S
          ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s)
          (Under.mk g) =
      originalArrowTransition F R s
        (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) :=
  originalTransition_reindex_source F f g s

example {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (originalCoefficientIso F (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (originalCoefficientRouteIso F f g).hom :=
  originalCoefficientIso_comp_hom F f g

example (R : C) :
    (originalCoefficientIso F (𝟙 R)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
          (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R)) ≫
        (Functor.leftUnitor (originalEvaluation F R)).hom =
      whiskerLeft (originalEvaluation F R) (F.mapId ⟨R⟩).hom.toNatTrans ≫
        (Functor.rightUnitor (originalEvaluation F R)).hom :=
  originalCoefficientIso_id F R

open CategoryTheory.GrothendieckFiber

example {R S : C} (f : R ⟶ S)
    {x x' : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (h : x = x') (φ : x'.val ⟶ y.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ] :
    liftedMap F f (eqToHom (congrArg Subtype.val h) ≫ φ) =
      (F.map f.toLoc).toFunctor.map (eqToHom (congrArg (originalObject F R) h)) ≫
        liftedMap F f φ :=
  liftedMap_precomp_eqToHom F f h φ

example {R S : C} (f : R ⟶ S)
    {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y y' : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (h : y = y') (φ : x.val ⟶ y.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ] :
    liftedMap F f (φ ≫ eqToHom (congrArg Subtype.val h)) =
      liftedMap F f φ ≫ eqToHom (congrArg (originalObject F S) h) :=
  liftedMap_postcomp_eqToHom F f h φ

variable (z : ∀ R : C, F.obj ⟨R⟩) (hz : ∀ R, IsZero (z R))
  (hm : ∀ {R S : C} (f : R ⟶ S), IsZero ((F.map f.toLoc).toFunctor.obj (z R)))

example {R S : C} (f : R ⟶ S) :
    (zeroNormalizedFunctor F z hz hm f).obj (z R) = z S :=
  zeroNormalizedFunctor_obj_zero F z hz hm f

example {R S : C} (f : R ⟶ S) :
    (zeroNormalizedCoefficientIso F z hz hm f).hom =
      (originalCoefficientIso F f).hom ≫
        whiskerLeft (originalEvaluation F R) (zeroNormalizationIso F z hz hm f).hom :=
  zeroNormalizedCoefficientIso_hom F z hz hm f

example {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (zeroNormalizedCoefficientIso F z hz hm (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation F R) (zeroNormalizedCoefficientCompIso F z hz hm f g).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (normalizedCoefficientRouteIso F f g (zeroNormalizationIso F z hz hm f)
            (zeroNormalizationIso F z hz hm g)).hom :=
  zeroNormalizedCoefficientIso_comp_hom F z hz hm f g

example (R : C) :
    (zeroNormalizedCoefficientIso F z hz hm (𝟙 R)).hom ≫
        whiskerLeft (originalEvaluation F R) (zeroNormalizedCoefficientIdIso F z hz hm R).hom ≫
        (Functor.rightUnitor (originalEvaluation F R)).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
        (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R)) ≫
          (Functor.leftUnitor (originalEvaluation F R)).hom :=
  zeroNormalizedCoefficientIso_id_hom F z hz hm R

/-- The normalized composition is exactly the original constraint with canonical rebasing. -/
example {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    zeroNormalizedCoefficientCompIso F z hz hm f g =
      (zeroNormalizationIso F z hz hm (f ≫ g)).symm ≪≫
        Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc) ≪≫
        isoWhiskerRight (zeroNormalizationIso F z hz hm f) (F.map g.toLoc).toFunctor ≪≫
        isoWhiskerLeft (zeroNormalizedFunctor F z hz hm f)
          (zeroNormalizationIso F z hz hm g) := rfl

/-- The normalized unit uses the original mapId, not an independent unit witness. -/
example (R : C) :
    zeroNormalizedCoefficientIdIso F z hz hm R =
      (zeroNormalizationIso F z hz hm (𝟙 R)).symm ≪≫
        Cat.Hom.toNatIso (F.mapId ⟨R⟩) := rfl

/-- A genuine pseudofunctor with nontrivial abelian-group fibers over all small types. -/
def groups : Pseudofunctor (LocallyDiscrete (Type)) Cat :=
  pseudofunctorOfIsLocallyDiscrete
    (fun _ => Cat.of AddCommGrpCat)
    (fun _ => (𝟭 AddCommGrpCat).toCatHom)
    (fun _ => Iso.refl _)
    (fun _ _ => Iso.refl _)

/-- The first and second coefficients both interchange the two elements. -/
def flip : Bool ⟶ Bool := TypeCat.ofHom fun b => !b

example : flip ≠ 𝟙 Bool := by
  intro h
  have h' := ConcreteCategory.congr_hom h false
  cases h'

/-- The composition equation is used for two actual nonidentity arrows and the integer fiber. -/
example :
    originalTransition groups Bool
        (cocartesianSection groups Bool (AddCommGrpCat.of ℤ)) (Under.mk (flip ≫ flip)) =
      (groups.mapComp flip.toLoc flip.toLoc).hom.toNatTrans.app
          ((originalEvaluation groups Bool).obj
            (cocartesianSection groups Bool (AddCommGrpCat.of ℤ))) ≫
        (groups.map flip.toLoc).toFunctor.map
          (originalTransition groups Bool
            (cocartesianSection groups Bool (AddCommGrpCat.of ℤ)) (Under.mk flip)) ≫
        originalArrowTransition groups Bool
          (cocartesianSection groups Bool (AddCommGrpCat.of ℤ))
          (Under.homMk flip : Under.mk flip ⟶ Under.mk (flip ≫ flip)) :=
  originalTransition_comp groups Bool flip flip _

end ColibTest.SectionTransitionCoherence
