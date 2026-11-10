/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionCoefficientIsoComponent
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionModel

/-! Actual support, chain-map comparison, exactness and zero for an arbitrary specified square. -/
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

example (s : BoundedAboveFlatAffineSections R) (hs : boundedAboveFlatAffineSectionSupported j s) :
    boundedAboveFlatAffineSectionSupported j' ((boundedAboveFlatAffineSectionsMap f).obj s) :=
  boundedAboveFlatAffineSectionsMap_supported j j' f l h s hs

example (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedSectionsMap j j' f l h).obj s).obj =
      (boundedAboveFlatAffineSectionsMap f).obj s.obj := rfl

example {s t : BoundedAboveFlatAffineSupportedSections j} (a : s ⟶ t) :
    ((boundedAboveFlatAffineSupportedSectionsMap j j' f l h).map a).hom =
      (boundedAboveFlatAffineSectionsMap f).map a.hom := rfl

example (s : BoundedAboveFlatAffineSupportedSections j) :
    (boundedAboveFlatPerfectSupported j').ι.map
        ((boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h).hom.app s) =
      (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
        ((eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
          (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm).hom.app s.obj) :=
  boundedAboveFlatAffineSupportedSectionCoefficientIso_hom_app j j' f l h s

example :
    IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j').cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j').weq
      (boundedAboveFlatAffineSupportedSectionsMap j j' f l h) :=
  boundedAboveFlatAffineSupportedSectionsMap_exact j j' f l h

example :
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h).obj
        (boundedAboveFlatAffineSupportedSectionZero j) =
      boundedAboveFlatAffineSupportedSectionZero j' :=
  boundedAboveFlatAffineSupportedSectionsMap_sectionZero j j' f l h

example :
    (boundedAboveFlatAffineSupportedSectionModelMap j j' f l h).hom.toFunctor =
      boundedAboveFlatAffineSupportedSectionsMap j j' f l h := rfl

example (j'' : W ⟶ Spec T) [IsOpenImmersion j'']
    (g : S ⟶ T) (m : W ⟶ V) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedAboveFlatAffineSupportedSectionModelMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedAboveFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedAboveFlatAffineSupportedSectionModelMap j' j'' g m hg :=
  boundedAboveFlatAffineSupportedSectionModelMap_comp j j' j'' f g l m h hg hfg
