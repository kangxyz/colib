/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

import Colib.CategoryTheory.Sites.Simplicial.ReducedCofiberExact
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeInclusionMono
import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# Reduced cochain sequences of the Tate quotient and cone

The collapse from the original Tate cone to the simplicial suspension
and the Laurent-open quotient both give short exact sequences of the
literal reduced cochains. The connecting map is that of the native
short-exact-sequence triangle of the quotient.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open CategoryTheory.PointedSimplicialPresheaf

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "C" => SmoothSite (Spec R)
local notation "J" => SmoothSite.nisnevichTopology (Spec R)

/-- Collapsing the affine-line term is the original pointed pushout to the suspension. -/
theorem tateConeToSuspension_isPushout :
    IsPushout (toPoint C (pointedAffineLine R))
      (toReducedMappingCofiber (pointedLaurentOpen R))
      (toReducedMappingCofiber (toPoint C (pointedTorus R))) (tateConeToSuspension R) := by
  let f := pointedLaurentOpen R
  let p := toPoint C (pointedAffineLine R)
  let g := toPoint C (pointedTorus R)
  let s : Arrow.mk f ⟶ Arrow.mk g :=
    Arrow.homMk (𝟙 _) p ((point_isZero C).eq_of_tgt _ _)
  have hp : f ≫ p = g := (point_isZero C).eq_of_tgt _ _
  have hc : reducedConeToMappingCofiber f ≫ tateConeToSuspension R =
      reducedConeToMappingCofiber g := by
    have h := reducedConeToMappingCofiber_map s
    change reducedConeToMappingCofiber f ≫ reducedMappingCofiberMap s =
      reducedConeMap (𝟙 (pointedTorus R)) ≫ reducedConeToMappingCofiber g at h
    change reducedConeToMappingCofiber f ≫ reducedMappingCofiberMap s = _
    exact h.trans (by rw [reducedConeMap_id, Category.id_comp])
  have outer : IsPushout (f ≫ p) (reducedConeInclusion (pointedTorus R))
      (toReducedMappingCofiber g)
      (reducedConeToMappingCofiber f ≫ tateConeToSuspension R) := by
    rw [hp, hc]
    exact reducedMappingCofiber_isPushout g
  exact IsPushout.of_left outer (toReducedMappingCofiber_map s).symm
    (reducedMappingCofiber_isPushout f)

private theorem mono_toTateCone_right :
    Mono (toReducedMappingCofiber (pointedLaurentOpen R)).right := by
  let F := PointedSimplicialPresheaf.forget C
  let : Mono (F.map (reducedConeInclusion (pointedTorus R))) :=
    mono_reducedConeInclusion_right (pointedTorus R)
  exact Adhesive.mono_of_isPushout_of_mono_right
    (F.map_isPushout (reducedMappingCofiber_isPushout (pointedLaurentOpen R)))

private theorem mono_pointedLaurentOpen_right :
    Mono (pointedLaurentOpen R).right := by
  let : Mono (multiplicativeGroupOpen (Spec R)) :=
    (forgetScheme (Spec R)).mono_of_mono_map
      (inferInstanceAs (Mono (multiplicativeGroupBaseChangeToAdditive (Spec R))))
  apply (NatTrans.mono_iff_mono_app _).2
  intro U
  apply (NatTrans.mono_iff_mono_app _).2
  intro n
  apply (CategoryTheory.mono_iff_injective _).2
  intro a b h
  exact (cancel_mono (multiplicativeGroupOpen (Spec R))).1 h

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}]

/-- The two original reduced-cochain maps of the Tate cone collapse
form a short exact sequence. -/
theorem exists_tateConeToSuspension_shortExact :
    let F := reducedCochains.{u + 1} C J
    let L := uliftPointed.{u + 1, u} C
    let i := F.map (L.map (toReducedMappingCofiber (pointedLaurentOpen R)))
    let q := F.map (L.map (tateConeToSuspension R))
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  let : Mono (toReducedMappingCofiber (pointedLaurentOpen R)).right := mono_toTateCone_right R
  let : Mono ((uliftPointed.{u + 1, u} C).map
      (toReducedMappingCofiber (pointedLaurentOpen R))).right :=
    mono_uliftPointed_map_right (toReducedMappingCofiber (pointedLaurentOpen R))
  exact exists_reducedCochains_shortExact_of_isPushout_isZero J
    (uliftPointed_map_isPushout.{u + 1, u} (tateConeToSuspension_isPushout R).flip)
    isZero_uliftPointed_point

/-- The original Laurent-open and Tate quotient maps form a short exact
sequence on reduced cochains. -/
theorem exists_tateSphereReducedCochains_shortExact :
    let F := reducedCochains.{u + 1} C J
    let L := uliftPointed.{u + 1, u} C
    let i := F.map (L.map (pointedLaurentOpen R))
    let q := F.map (L.map (toTateSphere R))
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  let : Mono (pointedLaurentOpen R).right := mono_pointedLaurentOpen_right R
  let : Mono ((uliftPointed.{u + 1, u} C).map (pointedLaurentOpen R)).right :=
    mono_uliftPointed_map_right (pointedLaurentOpen R)
  exact exists_reducedCochains_shortExact_of_isPushout_isZero J
    (uliftPointed_map_isPushout.{u + 1, u} (tateSphere_isPushout R)) isZero_uliftPointed_point

/-- The actual reduced-cochain sequence of the Tate quotient. -/
def tateSphereReducedCochainSequence :
    ShortComplex (CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ) :=
  let F := reducedCochains.{u + 1} C J
  let L := uliftPointed.{u + 1, u} C
  ShortComplex.mk (F.map (L.map (pointedLaurentOpen R))) (F.map (L.map (toTateSphere R)))
    (exists_tateSphereReducedCochains_shortExact R).choose

/-- The reduced-cochain sequence of the strict Tate quotient is short exact. -/
theorem tateSphereReducedCochainSequence_shortExact :
    (tateSphereReducedCochainSequence R).ShortExact :=
  (exists_tateSphereReducedCochains_shortExact R).choose_spec

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]

/-- The connecting map of the actual reduced-cochain sequence of the Tate quotient. -/
def tateSphereConnecting :
    (reducedDerivedChains.{d, u + 1} C J).obj ((uliftPointed.{u + 1, u} C).obj (tateSphere R)) ⟶
      ((reducedDerivedChains.{d, u + 1} C J).obj
        ((uliftPointed.{u + 1, u} C).obj (pointedTorus R)))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.triangleOfSES (tateSphereReducedCochainSequence_shortExact R)).mor₃

end AlgebraicGeometry.MotivicHomotopy
