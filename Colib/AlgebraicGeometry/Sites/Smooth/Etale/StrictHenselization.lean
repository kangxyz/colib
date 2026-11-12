/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Neighborhood
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase

import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# The original affine neighborhoods and the strict henselization

The marked affine neighborhoods used to evaluate smooth-site presheaves embed initially into
Stacks' size-bounded category of geometric-point neighborhoods. The embedding keeps the scheme,
structure map and marked lift. Restricting the native strict henselization cone therefore gives
a limit on the original neighborhood diagram, with its canonical structure map to the base
and canonical geometric point. A small cofiltered model retains the same affine stages.

The geometric-point compatibility proof adapts the global-sections computation in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationConeLift`
to arbitrary original affine neighborhoods, using the native general cone-leg germ formula.

The geometric point here has an algebraically closed field, as in the pinned Stacks definition.
No limit witness or cofinality hypothesis is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left) (s : GeometricPoint X.left)

include hX in
/-- The original affine neighborhoods fit inside the bounded site because they are étale. -/
theorem etaleNeighborhood_contains (A : EtaleNeighborhood X s.hom) :
    B.Contains ((etaleNeighborhoodToSmooth X s.hom).obj A).left :=
  (Scheme.size_le_of_locallyOfFiniteType (etaleNeighborhoodHom X s.hom A).left).trans_lt hX

/-- Include the original marked affine neighborhoods in Stacks' bounded neighborhood category. -/
def etaleNeighborhoodToBounded :
    EtaleNeighborhood X s.hom ⥤ (geometricPointFiber B X.left hX s).Elements where
  obj A := Functor.elementsMk _
    ⟨Over.mk (ObjectProperty.homMk (etaleNeighborhoodHom X s.hom A).left :
      B.obj ((etaleNeighborhoodToSmooth X s.hom).obj A).left
        (etaleNeighborhood_contains X B hX s A) ⟶ B.obj X.left hX),
      inferInstanceAs (Etale (etaleNeighborhoodHom X s.hom A).left)⟩
    ⟨etaleNeighborhoodMark X s.hom A, etaleNeighborhoodMark_hom X s.hom A⟩
  map {A C} f := Functor.Elements.homMk
    (ObjectProperty.homMk (Over.homMk
      (ObjectProperty.homMk ((etaleNeighborhoodToSmooth X s.hom).map f).left)
      (ObjectProperty.hom_ext _ (etaleNeighborhoodMap_hom X s.hom f))))
    (Subtype.ext (etaleNeighborhoodMark_map X s.hom f))

/-- The inclusion keeps the original scheme diagram, including all transition maps. -/
theorem etaleNeighborhoodToBounded_comp_diagram :
    etaleNeighborhoodToBounded X B hX s ⋙ etaleNeighborhoodDiagram B X.left hX s =
      etaleNeighborhoodToSmooth X s.hom ⋙ forgetScheme S := rfl

instance : (etaleNeighborhoodToBounded X B hX s).Faithful where
  map_injective {A C} f g h := by
    apply Functor.Elements.hom_ext
    apply (AffineEtale.Spec X.left).map_injective
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k ↦ (SmallEtale.toScheme B X.left hX).map k.hom) h

instance : (etaleNeighborhoodToBounded X B hX s).Full where
  map_surjective {A C} f := by
    let g := etaleNeighborhoodHomMk X s.hom
      ((SmallEtale.toScheme B X.left hX).map f.hom)
      (SmallEtale.toScheme_map_comp B X.left hX f.hom)
      (congrArg Subtype.val f.map_val)
    refine ⟨g, ?_⟩
    apply Functor.Elements.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact etaleNeighborhoodHomMk_map_left X s.hom _ _ _

/-- Every bounded neighborhood has a refinement by an original marked affine neighborhood. -/
theorem exists_etaleNeighborhoodToBounded_refinement
    (U : (geometricPointFiber B X.left hX s).Elements) :
    ∃ A, Nonempty ((etaleNeighborhoodToBounded X B hX s).obj A ⟶ U) := by
  let f := B.inclusion.map U.obj.obj.hom
  let : Etale f := U.obj.property
  obtain ⟨A, g, hg, hm⟩ :=
    exists_etaleNeighborhood_refinement X s.hom f U.val.val U.val.property
  exact ⟨A, ⟨Functor.Elements.homMk
    (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk g)
      (ObjectProperty.hom_ext _ hg))) (Subtype.ext hm)⟩⟩

/-- The actual affine-neighborhood inclusion is initial, without a cofinality assumption. -/
@[colib_tag "COL-1082", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/GeometricPointFiber.lean:147-151"
  "ingredient" "Cofiltered bounded geometric-point neighborhoods"]
instance initial_etaleNeighborhoodToBounded : (etaleNeighborhoodToBounded X B hX s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodToBounded X B hX s)
    (exists_etaleNeighborhoodToBounded_refinement X B hX s)

/-- The native strict henselization cone restricted to the original affine neighborhoods. -/
def etaleNeighborhoodStrictHenselizationCone :
    Cone (etaleNeighborhoodToSmooth X s.hom ⋙ forgetScheme S) :=
  (strictHenselizationCone B X.left hX s).whisker (etaleNeighborhoodToBounded X B hX s)

/-- The actual original neighborhood diagram has strict henselization as its limit. -/
@[colib_tag "COL-1082", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/HenselianRings/StrictHenselizationLimit.lean:407-409"
  "ingredient" "Native strict henselization limit restricted along the proved initial inclusion"]
def etaleNeighborhoodStrictHenselizationConeIsLimit :
    IsLimit (etaleNeighborhoodStrictHenselizationCone X B hX s) :=
  (Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodToBounded X B hX s)
    (strictHenselizationCone B X.left hX s)).symm
    (strictHenselizationConeIsLimit B X.left hX s)

/-- Every projection lies over the original smooth object by the canonical structure map. -/
@[colib_tag "COL-1082", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/HenselianRings/StrictHenselizationConeBase.lean:198-202"
  "ingredient" "The native cone leg agrees with the canonical strict henselization structure map",
  simp, reassoc]
theorem etaleNeighborhoodStrictHenselizationCone_π_comp_hom
    (A : EtaleNeighborhood X s.hom) :
    (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A ≫
        (etaleNeighborhoodHom X s.hom A).left = strictHenselizationToBase B X.left hX s :=
  strictHenselizationCone_π_comp_hom_eq B X.left hX s
    ((etaleNeighborhoodToBounded X B hX s).obj A)

/-- Each projection carries the canonical geometric point to the original marked lift. -/
@[colib_tag "COL-1082", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/StrictHenselizationConeLift.lean:44-67"
  "adaptation" "The cone-leg germ computation for arbitrary original affine neighborhoods",
  simp, reassoc]
theorem geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π
    (A : EtaleNeighborhood X s.hom) :
    geometricPointToStrictHenselization B X.left hX s ≫
        (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A =
      etaleNeighborhoodMark X s.hom A := by
  have : IsAffine ((etaleNeighborhoodToSmooth X s.hom ⋙ forgetScheme S).obj A) :=
    inferInstanceAs (IsAffine ((etaleNeighborhoodToSmooth X s.hom).obj A).left)
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom]
  ext b
  let π := (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A
  change (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom.hom
      ((geometricPointToStrictHenselization B X.left hX s).appTop.hom
        (π.appTop.hom b)) = _
  have hn := congrArg (fun φ ↦ CommRingCat.Hom.hom φ (π.appTop.hom b))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (structureSheafStalkToGeometricField B X.left hX s)))
  have h₂ := RingHom.congr_fun (structureSheafStalkToGeometricField_ι B X.left hX s
    (op ((etaleNeighborhoodToBounded X B hX s).obj A))) b
  exact hn.trans ((congrArg (structureSheafStalkToGeometricField B X.left hX s)
    (strictHenselizationCone_π_appTop B X.left hX s
      ((etaleNeighborhoodToBounded X B hX s).obj A) b)).trans h₂)

/-- A universe-small cofiltered index of original marked affine neighborhoods. -/
abbrev SmallEtaleNeighborhood :=
  InitiallySmall.CofilteredInitialModel.{u} (EtaleNeighborhood X s.hom)

/-- The canonical initial functor from the small model to the original neighborhoods. -/
abbrev smallEtaleNeighborhoodInclusion :
    SmallEtaleNeighborhood X s ⥤ EtaleNeighborhood X s.hom :=
  InitiallySmall.fromCofilteredInitialModel.{u} (EtaleNeighborhood X s.hom)

/-- The same original smooth-site neighborhoods, now with a universe-small index. -/
abbrev smallEtaleNeighborhoodToSmooth : SmallEtaleNeighborhood X s ⥤ SmoothSite S :=
  smallEtaleNeighborhoodInclusion X s ⋙ etaleNeighborhoodToSmooth X s.hom

/-- The native strict henselization cone on the small original affine neighborhood diagram. -/
def smallEtaleNeighborhoodStrictHenselizationCone :
    Cone (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S) :=
  (etaleNeighborhoodStrictHenselizationCone X B hX s).whisker
    (smallEtaleNeighborhoodInclusion X s)

/-- The small original neighborhood diagram has the native strict henselization as its limit. -/
@[colib_tag "COL-1082", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/HenselianRings/StrictHenselizationLimit.lean:407-409"
  "ingredient" "Native strict henselization limit on small original affine neighborhoods"]
def smallEtaleNeighborhoodStrictHenselizationConeIsLimit :
    IsLimit (smallEtaleNeighborhoodStrictHenselizationCone X B hX s) :=
  (Functor.Initial.isLimitWhiskerEquiv (smallEtaleNeighborhoodInclusion X s)
    (etaleNeighborhoodStrictHenselizationCone X B hX s)).symm
    (etaleNeighborhoodStrictHenselizationConeIsLimit X B hX s)

/-- Every stage of the small original diagram is affine. -/
instance (a : SmallEtaleNeighborhood X s) :
    IsAffine ((smallEtaleNeighborhoodToSmooth X s).obj a).left :=
  inferInstanceAs
    (IsAffine ((etaleNeighborhoodToSmooth X s.hom).obj
      ((smallEtaleNeighborhoodInclusion X s).obj a)).left)

/-- The small cone retains the original structure map to the selected smooth object. -/
@[simp, reassoc]
theorem smallEtaleNeighborhoodStrictHenselizationCone_π_comp_hom
    (a : SmallEtaleNeighborhood X s) :
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a ≫
        (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a)).left =
      strictHenselizationToBase B X.left hX s :=
  etaleNeighborhoodStrictHenselizationCone_π_comp_hom X B hX s _

/-- The small cone retains the original geometric marking at each stage. -/
@[simp, reassoc]
theorem geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π
    (a : SmallEtaleNeighborhood X s) :
    geometricPointToStrictHenselization B X.left hX s ≫
        (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a =
      etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a) :=
  geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π X B hX s _

end AlgebraicGeometry.Scheme.SmoothSite
