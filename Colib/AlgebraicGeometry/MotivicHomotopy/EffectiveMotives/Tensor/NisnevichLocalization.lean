/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichLift
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveExact
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
import Mathlib.CategoryTheory.Localization.Adjunction
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
import StacksFrontier.CategoryTheory.Triangulated.Quotient
import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Bounded-above Nisnevich localization of derived transfer presheaves

Exact Nisnevich sheafification localizes the unbounded derived category by
its kernel. Upper truncations preserve this kernel, giving the bounded-above
localization on the same sheaf complexes and actual sheafification maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "a(" K ")" => derivedNisnevichSheafification K
set_option quotPrecheck false in
local notation "aD(" K ")" => (nisnevichSheafify K).mapDerivedCategory
local notation "a₀(" K ")" => nisnevichSheafify K
set_option quotPrecheck false in
local notation "t(" K ")" => (DerivedCategory.TStructure.t (C := PST(K)))

/-- The canonical abelian structure on the sheaf target. -/
local instance instAbelianNisnevichLocalization : Abelian NST(k) := SheafWithTransfers.abelian k

private instance : (aD(k)).kernel.IsClosedUnderIsomorphisms :=
  ⟨fun e h => h.of_iso ((aD(k)).mapIso e).symm⟩

instance : (aD(k)).kernel.IsTriangulated := (aD(k)).isTriangulated_and_isSaturated_kernel.1

private theorem isIso_map_iff_trW_kernel {K L : DerivedCategory PST(k)} (f : K ⟶ L) :
    IsIso ((aD(k)).map f) ↔ (aD(k)).kernel.trW f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  exact ((ObjectProperty.trW_iff_of_distinguished (aD(k)).kernel T hT).trans
    (Triangle.isZero₃_iff_isIso₁ ((aD(k)).mapTriangle.obj T) ((aD(k)).map_distinguished T hT))).symm

private instance : (aD(k)).IsLocalization (aD(k)).kernel.trW := by
  let adj := nisnevichDerivedAdjunction k
  let R := forgetDerivedFunctor k
  let e : R.FullyFaithful := adj.fullyFaithfulROfIsIsoCounit
  let : R.Full := e.full
  let : R.Faithful := e.faithful
  have h := adj.isLocalization
  have he : (MorphismProperty.isomorphisms (DerivedCategory NST(k))).inverseImage (aD(k)) =
      (aD(k)).kernel.trW := by
    ext X Y f
    exact isIso_map_iff_trW_kernel k f
  exact he ▸ h

private theorem truncLE_mem_sheafification_kernel (b : ℤ) (K : DerivedCategory PST(k))
    (hK : (aD(k)).kernel K) : (aD(k)).kernel (((t(k)).truncLE b).obj K) := by
  change IsZero ((aD(k)).obj (((t(k)).truncLE b).obj K))
  apply (DerivedCategory.isZero_iff_forall_isZero_homology _).2
  intro n
  let L := ((t(k)).truncLE b).obj K
  let H := DerivedCategory.homologyFunctor PST(k) n
  let H' := DerivedCategory.homologyFunctor NST(k) n
  by_cases hn : n ≤ b
  · let : IsIso (H.map (((t(k)).truncLEι b).app K)) :=
      Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app b n hn K
    let e := ((a₀(k)).mapDerivedCategoryHomologyIso n).app L ≪≫
      (a₀(k)).mapIso (asIso (H.map (((t(k)).truncLEι b).app K))) ≪≫
      ((a₀(k)).mapDerivedCategoryHomologyIso n).symm.app K
    exact (H'.map_isZero hK).of_iso e
  · exact ((a₀(k)).map_isZero (DerivedCategory.isZero_of_isLE L b n (by omega))).of_iso
      (((a₀(k)).mapDerivedCategoryHomologyIso n).app L)

private instance : (t(k)).minus.IsVerdierLeftLocalizing (aD(k)).kernel where
  fac {X Y} f hX hY := by
    obtain ⟨b, hb⟩ := hX
    let : (t(k)).IsLE X b := hb
    exact ⟨((t(k)).truncLE b).obj Y, (t(k)).liftTruncLE f b, ((t(k)).truncLEι b).app Y,
      ⟨b, inferInstance⟩, truncLE_mem_sheafification_kernel k b Y hY, (t(k)).liftTruncLE_ι f b⟩

/-- The Nisnevich-acyclic bounded-above transfer presheaf complexes. -/
abbrev nisnevichDerivedMinusKernel : ObjectProperty (DerivedCategory.Minus PST(k)) :=
  (aD(k)).kernel.inverseImage (DerivedCategory.Minus.ι (C := PST(k)))

/-- Bounded-above sheafification is the Verdier localization at its
Nisnevich-acyclic complexes, with the original localization functor. -/
instance derivedNisnevichSheafification_isLocalization :
    (derivedNisnevichSheafification k).IsLocalization (nisnevichDerivedMinusKernel k).trW := by
  let : (derivedNisnevichSheafification k).EssSurj :=
    ⟨fun K => ⟨presheafLift k K, ⟨sheafificationPresheafLiftIso k K⟩⟩⟩
  let Φ := (t(k)).minus.triangulatedLocalizerMorphism (aD(k)).kernel
  exact Φ.isLocalization_of_isLocalizedFullyFaithful
    (L₂ := aD(k)) (F := DerivedCategory.Minus.ι) (Iso.refl _)

/-- A bounded Nisnevich morphism is inverted exactly when its cone is
Nisnevich-acyclic. -/
theorem isIso_derivedNisnevichSheafification_map_iff
    {K L : DerivedCategory.Minus PST(k)} (f : K ⟶ L) :
    IsIso ((derivedNisnevichSheafification k).map f) ↔ (nisnevichDerivedMinusKernel k).trW f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  let A := derivedNisnevichSheafification k
  have he : (nisnevichDerivedMinusKernel k) T.obj₃ ↔ IsZero (A.obj T.obj₃) :=
    ⟨fun hZ => IsZero.of_full_of_faithful_of_isZero DerivedCategory.Minus.ι _ hZ,
      fun hZ => DerivedCategory.Minus.ι.map_isZero hZ⟩
  let e := Triangle.isZero₃_iff_isIso₁ (A.mapTriangle.obj T) (A.map_distinguished T hT)
  exact ((ObjectProperty.trW_iff_of_distinguished (nisnevichDerivedMinusKernel k) T hT).trans
    (he.trans e)).symm

end AlgebraicGeometry.MotivicHomotopy
