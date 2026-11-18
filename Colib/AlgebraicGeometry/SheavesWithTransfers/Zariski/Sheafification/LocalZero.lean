/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Zariski.Topology
public import Colib.CategoryTheory.Sites.SheafifyLocallyZero
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Field
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse

/-!
# Zariski local vanishing of homotopy invariant presheaves with transfers

Generic open zero restrictions give zero neighborhoods at every original
point. The chosen neighborhoods form a smooth Zariski covering family.
A Nisnevich-local zero restriction gives a generic open zero restriction
on each integral affine smooth model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- On the smooth site, ordinary abelian sheafification in the site universe
inverts the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_addCommGrpCat {S : Scheme.{u}}
    (J : GrothendieckTopology (SmoothSite S)) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  @CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall
    (SmoothSite S) _ J (inferInstance : EssentiallySmall.{u + 1} (SmoothSite S))

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "JZar" => SmoothSite.zariskiTopology (Spec (CommRingCat.of k))
local notation "JNis" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))

/-- The equalizer sieve is Zariski covering when the sections have generic
open zeros and the transfer presheaf is homotopy invariant. -/
theorem zeroSieve_mem_zariskiTopology_of_generic_open_zeros
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) (hG : P.HasGenericOpenZeros)
    (X : SmoothSite (Spec (.of k))) (s : ((toPresheaf k).obj P).obj (op X)) :
    Presheaf.equalizerSieve s 0 ∈ JZar X := by
  choose O _ hx hz using fun x =>
    P.exists_zero_neighborhood_of_generic_open_zeros
      (integralAffineLocalZero_of_field k) hP hG X s x
  let V (x : X.left) := (SmoothSite.opensFunctor X).obj (O x)
  let f (x : X.left) : V x ⟶ X := SmoothSite.openInclusion X (O x)
  refine SmoothSite.mem_zariskiTopology_iff.mpr ⟨Presieve.ofArrows V f, ?_, ?_⟩
  · exact (SmoothSite.ofArrows_mem_zariskiPrecoverage_iff f).mpr
      ⟨fun x => ⟨x, ⟨x, hx x⟩, rfl⟩, fun x =>
        inferInstanceAs (IsOpenImmersion (O x).ι)⟩
  · rw [Presieve.ofArrows_le_iff]
    intro x
    change transfer P ((Cor.graphFunctor k).map (f x)) s =
      transfer P ((Cor.graphFunctor k).map (f x)) 0
    rw [map_zero]
    exact hz x

/-- Vanishing on actual generic open neighborhoods forces zero ordinary
Zariski sheafification of the graph restriction. -/
theorem isZero_zariskiSheafify_of_generic_open_zeros
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) (hG : P.HasGenericOpenZeros) :
    IsZero ((presheafToSheaf JZar AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)) := by
  let := SmoothSite.wEqualsLocallyBijective_addCommGrpCat JZar
  exact Presheaf.isZero_sheafify_of_locally_zero JZar ((toPresheaf k).obj P)
    (zeroSieve_mem_zariskiTopology_of_generic_open_zeros P hP hG)

/-- A Nisnevich-locally-zero homotopy invariant transfer presheaf has zero
ordinary Zariski sheafification over any field. -/
theorem isZero_zariskiSheafify_of_nisnevich_locally_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (h : ∀ (X : SmoothSite (Spec (.of k))) (s : ((toPresheaf k).obj P).obj (op X)),
      Presheaf.equalizerSieve s 0 ∈ JNis X) :
    IsZero ((presheafToSheaf JZar AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)) := by
  apply isZero_zariskiSheafify_of_generic_open_zeros P hP
  intro T _ _ s
  obtain ⟨O, hO, hz⟩ := SmoothSite.exists_generic_open_mem_covering_sieve
    T (Presheaf.equalizerSieve (F := (toPresheaf k).obj P) (X := op T) s 0) (h T s)
  refine ⟨O, hO, ?_⟩
  change transfer P ((Cor.graphFunctor k).map (SmoothSite.openInclusion T O)) s = 0
  change transfer P ((Cor.graphFunctor k).map (SmoothSite.openInclusion T O)) s =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.openInclusion T O)) 0 at hz
  simpa only [map_zero] using hz

/-- An invariant transfer presheaf with zero ordinary Nisnevich sheafification
has zero ordinary Zariski sheafification. -/
theorem isZero_zariskiSheafify_of_isZero_nisnevichSheafify
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (h : IsZero ((presheafToSheaf JNis AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P))) :
    IsZero ((presheafToSheaf JZar AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)) := by
  apply isZero_zariskiSheafify_of_nisnevich_locally_zero P hP
  intro X s
  let E := sheafToPresheaf JNis AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op X)
  let hs : Subsingleton ((sheafify JNis ((toPresheaf k).obj P)).obj (op X)) :=
    AddCommGrpCat.subsingleton_of_isZero (E.map_isZero h)
  let := SmoothSite.wEqualsLocallyBijective_addCommGrpCat JNis
  let := ((JNis).W_toSheafify ((toPresheaf k).obj P)).isLocallyInjective
  exact Presheaf.equalizerSieve_mem JNis (toSheafify JNis ((toPresheaf k).obj P))
    (X := op X) s 0 (@Subsingleton.elim _ hs _ _)

end AlgebraicGeometry.PresheafWithTransfers
