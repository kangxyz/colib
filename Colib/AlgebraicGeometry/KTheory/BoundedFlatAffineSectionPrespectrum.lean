/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionWaldhausen
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-!
# The strict affine bounded-above-flat section prespectrum functor

Actual section objects and morphisms both lie in universe `u + 1`. Their original category
therefore gives a native small Waldhausen category directly, with no old model wrapper or
supplied geometric profile. Literal reindexing, exactness and chosen-zero equality establish
the strict model functor before application of the actual iterated-S prespectrum functor.

The geometric evaluation has a smaller hom universe. This file does not assign a K-map to
that raw mixed-universe functor, nor assert an evaluation stable equivalence, coefficient
comparison homotopy, Laurent seed, negative localization or Thomason--Trobaugh 7.4.

Adapted from Quillen's `BoundedFlat/SectionPrespectrum.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining native small-category constructions.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original section category is already small in object and hom universe `u + 1`. -/
def boundedAboveFlatAffineSectionModel (R : CommRingCat.{u}) :
    WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatAffineSections R,
     waldhausen := boundedAboveFlatAffineSectionWaldhausen R }⟩

/-- Every coefficient restriction is exact and preserves the original chosen zero literally. -/
def boundedAboveFlatAffineSectionModelMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionModel R ⟶ boundedAboveFlatAffineSectionModel S :=
  ⟨⟨boundedAboveFlatAffineSectionsMap f, boundedAboveFlatAffineSectionsMap_exact f⟩,
    boundedAboveFlatAffineSectionsMap_sectionZero f⟩

/-- The native model map retains the actual literal coefficient restriction functor. -/
theorem boundedAboveFlatAffineSectionModelMap_toFunctor {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionModelMap f).hom.toFunctor =
      boundedAboveFlatAffineSectionsMap f := rfl

/-- Actual section models form a strict functor on all commutative ring maps. -/
@[colib_tag "COL-0355",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionPrespectrum.lean:31-59"
    "adaptation" "Native small section models and their strict coefficient prespectrum functor"]
def boundedAboveFlatAffineSectionModelFunctor :
    CommRingCat.{u} ⥤ WideSubcategory preservesZero.{u + 1} where
  obj := boundedAboveFlatAffineSectionModel
  map := boundedAboveFlatAffineSectionModelMap
  map_id R := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatAffineSectionsMap_id R
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatAffineSectionsMap_comp f g

/-- The original iterated-S realization applied to the actual strict section model functor. -/
@[colib_tag "COL-0355"]
def boundedAboveFlatAffineSectionPrespectrumFunctor :
    CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1} :=
  boundedAboveFlatAffineSectionModelFunctor ⋙ prespectrumFunctor

/-- The coefficient prespectrum retains literal identity maps, before passing to homotopy. -/
theorem boundedAboveFlatAffineSectionPrespectrumFunctor_map_id (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.map (𝟙 R) =
      𝟙 (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R) :=
  boundedAboveFlatAffineSectionPrespectrumFunctor.map_id R

/-- Coefficient prespectrum composition is a literal equality of whole prespectrum maps. -/
theorem boundedAboveFlatAffineSectionPrespectrumFunctor_map_comp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffineSectionPrespectrumFunctor.map g :=
  boundedAboveFlatAffineSectionPrespectrumFunctor.map_comp f g

/-- The zero-space homotopy sets retain the actual section Waldhausen K-groups. -/
def boundedAboveFlatAffineSectionZeroSpaceEquiv (R : CommRingCat.{u}) (n : ℕ) :
    (boundedAboveFlatAffineSectionWaldhausen R).K n ≃
      HomotopyGroup.Pi n ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0)
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point 0) :=
  zeroSpaceHomotopyEquiv (boundedAboveFlatAffineSectionModel R) n

/-- The original coefficient K-map is the induced zero-space map, including degree zero. -/
@[colib_tag "COL-0355"]
theorem boundedAboveFlatAffineSectionZeroSpaceEquiv_naturality {R S : CommRingCat.{u}}
    (f : R ⟶ S) (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffineSectionZeroSpaceEquiv S n
        (KMap (boundedAboveFlatAffineSectionsMap_exact f) n a) =
      HomotopyGroup.map ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map 0)
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a) := by
  rw [KMap_eq_piMap_of_zeroEq (boundedAboveFlatAffineSectionsMap_exact f)
    (boundedAboveFlatAffineSectionModelMap f).property]
  exact loopShiftEquiv_natural n (deloopingMap (boundedAboveFlatAffineSectionsMap_exact f)).hom
    (stageMap_point 0 (boundedAboveFlatAffineSectionModelMap f)) a

end AlgebraicGeometry.Scheme.Modules
