/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenFibration
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenSupport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence
public import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality
public import Colib.KTheory.Waldhausen.ExactEquivalence

/-! # Naturality of the relative boundary and its literal bounded-flat comparison

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ConnectingNaturality.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
universe u
namespace AlgebraicGeometry.Scheme.Modules

section
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original equivalence from relative acyclic objects to supported flat complexes. -/
def boundedAboveFlatPerfectAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).K n ≃*
      BoundedAboveFlatPerfectSupportedK j n :=
  KEquivOfExactEquivalence (boundedAboveFlatPerfectAcyclicSupportedEquivalence j)
    (boundedAboveFlatPerfectAcyclicToSupported_exact j)
    (boundedAboveFlatPerfectSupportedToAcyclic_exact j) n

/-- The genuine bounded-flat relative-to-supported boundary. -/
def boundedAboveFlatPerfectOpenConnectingHom (n : ℕ) :
    BoundedAboveFlatPerfectOpenK j (n + 1) →* BoundedAboveFlatPerfectSupportedK j n :=
  (boundedAboveFlatPerfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
    (changeWeakConnectingHom (boundedAboveFlatPerfectOpenNested j)
      (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n)

end

/-- Flattening the actual relative-acyclic objects commutes with geometric pullback. -/
theorem boundedAboveFlatPerfectAcyclicSupportedKEquiv_pullback
    {A B : AlgebraicGeometry.Scheme.OpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    (boundedAboveFlatPerfectSupportedKPullback f n).comp
      (boundedAboveFlatPerfectAcyclicSupportedKEquiv B.hom n).toMonoidHom =
    (boundedAboveFlatPerfectAcyclicSupportedKEquiv A.hom n).toMonoidHom.comp
      (KMap (acyclicFunctor_exact (boundedAboveFlatPerfectOpenNested B.hom)
      (boundedAboveFlatPerfectOpenNested A.hom)
      (boundedAboveFlatPerfectPullback_isExact f.right)
        (boundedAboveFlatPerfectOpenPullback_isExact f)) n) := by
  change (KMap (boundedAboveFlatPerfectSupportedPullback_isExact f) n).comp
      (KMap (boundedAboveFlatPerfectAcyclicToSupported_exact B.hom) n) =
    (KMap (boundedAboveFlatPerfectAcyclicToSupported_exact A.hom) n).comp _
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

/-- The original supported boundary commutes with arbitrary open-pair pullback. -/
theorem boundedAboveFlatPerfectOpenConnectingHom_pullback
    {A B : AlgebraicGeometry.Scheme.OpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    (boundedAboveFlatPerfectSupportedKPullback f n).comp
        (boundedAboveFlatPerfectOpenConnectingHom B.hom n) =
      (boundedAboveFlatPerfectOpenConnectingHom A.hom n).comp
        (boundedAboveFlatPerfectOpenKPullback f (n + 1)) := by
  unfold boundedAboveFlatPerfectOpenConnectingHom boundedAboveFlatPerfectOpenKPullback
  rw [← MonoidHom.comp_assoc, boundedAboveFlatPerfectAcyclicSupportedKEquiv_pullback,
    MonoidHom.comp_assoc, changeWeakConnectingHom_natural
      (boundedAboveFlatPerfectOpenNested B.hom) (boundedAboveFlatPerfectOpenNested A.hom)
      (boundedAboveFlatPerfectPullback_isExact f.right)
      (boundedAboveFlatPerfectOpenPullback_isExact f)
      (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence B.hom)
      (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence A.hom) n,
    ← MonoidHom.comp_assoc]

/-- Original bounded-flat inclusion and acyclic flattening commute literally on K-maps. -/
theorem boundedAboveFlatPerfectAcyclicSupportedKEquiv_comparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (boundedAboveFlatPerfectSupportedToPerfectKMap j n).comp
      (boundedAboveFlatPerfectAcyclicSupportedKEquiv j n).toMonoidHom =
    (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
      (KMap (acyclicFunctor_exact (boundedAboveFlatPerfectOpenNested j) (perfectOpenNested j)
        (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace)
        (boundedAboveFlatPerfectOpenInclusion_isExact j))
        n) := by
  change (KMap (boundedAboveFlatPerfectSupportedInclusion_isExact j) n).comp
      (KMap (boundedAboveFlatPerfectAcyclicToSupported_exact j) n) =
    (KMap (perfectAcyclicToSupported_exact j) n).comp _
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

/-- The actual inclusion compares the original supported boundaries, without qc assumptions. -/
theorem boundedAboveFlatPerfectOpenConnectingHom_comparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (boundedAboveFlatPerfectSupportedToPerfectKMap j n).comp
      (boundedAboveFlatPerfectOpenConnectingHom j n) =
    (perfectOpenConnectingHom j n).comp
        (boundedAboveFlatPerfectOpenToPerfectOpenKMap j (n + 1)) := by
  unfold boundedAboveFlatPerfectOpenConnectingHom perfectOpenConnectingHom
    boundedAboveFlatPerfectOpenToPerfectOpenKMap
  rw [← MonoidHom.comp_assoc, boundedAboveFlatPerfectAcyclicSupportedKEquiv_comparison,
    MonoidHom.comp_assoc, changeWeakConnectingHom_natural
      (boundedAboveFlatPerfectOpenNested j) (perfectOpenNested j)
      (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace)
        (boundedAboveFlatPerfectOpenInclusion_isExact j)
      (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n,
    ← MonoidHom.comp_assoc]

end AlgebraicGeometry.Scheme.Modules
