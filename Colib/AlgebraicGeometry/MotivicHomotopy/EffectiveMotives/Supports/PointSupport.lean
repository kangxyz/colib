/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.RepresentedCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ComplementComparison
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.Order.LatticeIntervals

/-! # Cohomology supported at a point

The point group is the colimit over ambient open neighbourhoods, with closed
support the intersection with the closure of the point. Each stage uses the
original relative motive of the complementary open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

/-- Actual ambient open neighbourhoods of a point, ordered by inclusion. -/
abbrev PointSupportNeighborhoods (x : X.left) := OpenNhds (X := X.left.carrier) x

/-- The part of an ambient open outside the closure of the indicated point. -/
def pointSupportComplement (x : X.left) (U : X.left.Opens) : X.left.Opens :=
  U ⊓ (Closeds.closure {x}).compl

/-- The original inclusion of the complement into an ambient neighbourhood. -/
def pointSupportPair (x : X.left) (U : PointSupportNeighborhoods k X x) : Arrow Sm(k) :=
  Arrow.mk ((SmoothSite.opensFunctor X).map
    (homOfLE (inf_le_left : pointSupportComplement k X x U.1 ≤ U.1)))

instance (x : X.left) (U : PointSupportNeighborhoods k X x) :
    IsOpenImmersion (pointSupportPair k X x U).hom.left := by
  change IsOpenImmersion (X.left.homOfLE
    (inf_le_left : pointSupportComplement k X x U.1 ≤ U.1))
  infer_instance

/-- The actual pairs on open neighbourhoods, with their inclusions. -/
def pointSupportPairFunctor (x : X.left) : PointSupportNeighborhoods k X x ⥤ Arrow Sm(k) where
  obj U := pointSupportPair k X x U
  map {U V} f := Arrow.homMk'
    ((SmoothSite.opensFunctor X).map
      (homOfLE (inf_le_inf_right (Closeds.closure {x}).compl f.le)))
    ((SmoothSite.opensFunctor X).map (homOfLE f.le)) (by
      change _ ≫ (SmoothSite.opensFunctor X).map _ = (SmoothSite.opensFunctor X).map _ ≫ _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)
  map_id _ := by
    apply Arrow.hom_ext <;> exact (SmoothSite.opensFunctor X).map_id _
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (SmoothSite.opensFunctor X).map_comp
        (homOfLE (inf_le_inf_right (Closeds.closure {x}).compl f.le))
        (homOfLE (inf_le_inf_right (Closeds.closure {x}).compl g.le))
    · exact (SmoothSite.opensFunctor X).map_comp (homOfLE f.le) (homOfLE g.le)

/-- A closed immersion with the range of the restricted point closure gives
its usual complementary open pair. -/
def pointSupportPairIso (x : X.left) (U : PointSupportNeighborhoods k X x)
    {Z : Scheme.{u}} (z : Z ⟶ ((SmoothSite.opensFunctor X).obj U.1).left)
    [IsClosedImmersion z]
    (hz : Set.range z = Scheme.Opens.ι (X := X.left) U.1 ⁻¹' closure {x}) :
    pointSupportPair k X x U ≅ Arrow.mk (SmoothSite.closedPairOpenInclusion z) := by
  let j := (pointSupportPair k X x U).hom
  let hj : IsOpenImmersion j.left := inferInstanceAs
    (IsOpenImmersion (pointSupportPair k X x U).hom.left)
  let Y := (SmoothSite.opensFunctor X).obj U.1
  let a := SmoothSite.closedPairOpenInclusion (X := Y) z
  let ha : IsOpenImmersion a.left := inferInstanceAs
    (IsOpenImmersion (Scheme.Opens.ι (X := Y.left) (SmoothSite.closedPairOpen (X := Y) z)))
  have hr : Set.range j.left = Set.range a.left := by
    change Set.range (X.left.homOfLE
      (inf_le_left : pointSupportComplement k X x U.1 ≤ U.1)) =
        Set.range (SmoothSite.closedPairOpenInclusion (X := Y) z).left
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE,
      SmoothSite.range_closedPairOpenInclusion, hz]
    ext y
    exact ⟨fun hy ↦ hy.2, fun hy ↦ ⟨y.2, hy⟩⟩
  exact @SmoothSite.openInclusionArrowIso _ _ _ _ j a hj ha hr

/-- Inclusion of the neighbourhoods contained in one fixed neighbourhood. -/
def pointSupportSubneighborhoodInclusion (x : X.left) (U : PointSupportNeighborhoods k X x) :
    (Set.Iic U)ᵒᵖ ⥤ (PointSupportNeighborhoods k X x)ᵒᵖ :=
  (Subtype.mono_coe (· ≤ U)).functor.op

/-- Intersecting with the fixed neighbourhood makes the subdiagram cofinal. -/
instance (x : X.left) (U : PointSupportNeighborhoods k X x) :
    (pointSupportSubneighborhoodInclusion k X x U).Final := by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro V
    have h : V.unop ⊓ U ≤ U := inf_le_right
    refine ⟨op (⟨V.unop ⊓ U, Set.mem_Iic.mpr h⟩ : Set.Iic U), ⟨?_⟩⟩
    exact (homOfLE (inf_le_left : V.unop ⊓ U ≤ V.unop)).op
  · intro _ W _ _
    exact ⟨W, 𝟙 _, Subsingleton.elim _ _⟩

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

/-- The cohomology diagram that restricts supported classes to smaller neighbourhoods. -/
abbrev pointSupportCohomologyDiagram (K : DM(k)) (n : ℤ) (x : X.left) :
    (PointSupportNeighborhoods k X x)ᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  (pointSupportPairFunctor k X x).op ⋙ effectivePairCohomology k K n

variable [UnivLE.{u, w'}]

/-- The degree `n` support cohomology at a point. -/
abbrev pointSupportCohomology (K : DM(k)) (n : ℤ) (x : X.left) : AddCommGrpCat.{w'} :=
  colimit (pointSupportCohomologyDiagram k X K n x)

/-- A class on any actual open neighbourhood gives a class supported at the point. -/
abbrev pointSupportι (K : DM(k)) (n : ℤ) (x : X.left)
    (U : PointSupportNeighborhoods k X x) :
    (pointSupportCohomologyDiagram k X K n x).obj (op U) ⟶ pointSupportCohomology k X K n x :=
  colimit.ι _ (op U)

/-- The same point group can be computed inside a fixed ambient neighbourhood. -/
def pointSupportSubneighborhoodColimitIso (K : DM(k)) (n : ℤ) (x : X.left)
    (U : PointSupportNeighborhoods k X x) :
    colimit (pointSupportSubneighborhoodInclusion k X x U ⋙
      pointSupportCohomologyDiagram k X K n x) ≅ pointSupportCohomology k X K n x :=
  Functor.Final.colimitIso _ _

end AlgebraicGeometry.MotivicHomotopy
