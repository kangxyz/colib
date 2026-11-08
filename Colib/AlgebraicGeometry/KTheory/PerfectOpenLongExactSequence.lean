/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenFibration
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-!
# The original supported inclusion in the relative-open long exact sequence

The native relative-coarse fibration and explicit exact supported equivalence
give all three positions of the connective long exact sequence. The inclusion
is literally the existing `perfectSupportedKMap`; the target is the named
`PerfectOpenK`, not fine perfect-complex K-theory on U. In particular relative degree-zero
surjectivity below makes no surjectivity claim for open restriction.
-/
@[expose] public section

open CategoryTheory.Waldhausen

/-! Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/OpenLongExactSequence.lean`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The genuine homotopy-fiber boundary in the original supported K-groups. -/
def perfectOpenConnectingHom (n : ℕ) : PerfectOpenK j (n + 1) →* PerfectSupportedK j n :=
  (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
    (changeWeakConnectingHom (perfectOpenNested j)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n)

/-- The original supported K-groups map to the actual canonical homotopy fiber. -/
def perfectSupportedFiberKMap (n : ℕ) : PerfectSupportedK j n →*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (changeWeakMap (perfectOpenNested j))
        (perfectOpenWeakWaldhausen j).kBasepoint)
      (HomotopyFiber.basepoint (changeWeakMap (perfectOpenNested j))
        (perfectOpenWeakWaldhausen j).kBasepoint
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint
        (changeWeakMap_basepoint (perfectOpenNested j))) :=
  (canonicalFiberKMap (perfectOpenNested j) n).comp
    (perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom

/-- The supported-to-fiber map is bijective in every connective K-degree. -/
theorem perfectSupportedFiberKMap_bijective (n : ℕ) :
    Function.Bijective (perfectSupportedFiberKMap j n) :=
  (canonicalFiberKMap_bijective_of_weak (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n).comp
    (perfectAcyclicSupportedKEquiv j n).symm.bijective

/-- Projection of the actual fiber map is precisely the existing supported inclusion. -/
theorem perfectSupportedFiberKMap_projection (n : ℕ) :
    (HomotopyGroup.piMap n (HomotopyFiber.projection (changeWeakMap (perfectOpenNested j))
      (perfectOpenWeakWaldhausen j).kBasepoint)
      (HomotopyFiber.projection_basepoint _ _
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint
        (changeWeakMap_basepoint (perfectOpenNested j)))).comp
      (perfectSupportedFiberKMap j n) = perfectSupportedKMap j n := by
  rw [perfectSupportedFiberKMap, ← MonoidHom.comp_assoc]
  erw [canonicalFiberKMap_projection]
  exact perfectAcyclicSupportedKEquiv_symm_inclusion j n

/-- The transported boundary has the original full canonical homotopy-fiber boundary. -/
theorem perfectSupportedFiberKMap_connecting (n : ℕ) (a : PerfectOpenK j (n + 1)) :
    perfectSupportedFiberKMap j n (perfectOpenConnectingHom j n a) =
      HomotopyFiber.connectingHom (changeWeakMap (perfectOpenNested j))
        (perfectOpenWeakWaldhausen j).kBasepoint
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint
        (changeWeakMap_basepoint (perfectOpenNested j)) n a := by
  change canonicalFiberKMap (perfectOpenNested j) n
    ((perfectAcyclicSupportedKEquiv j n).symm
      (perfectAcyclicSupportedKEquiv j n
        (changeWeakConnectingHom (perfectOpenNested j)
          (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n a))) = _
  rw [MulEquiv.symm_apply_apply]
  exact canonicalFiberKMap_connecting (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n a

/-- Exactness at the original perfect K-group, with its existing supported inclusion. -/
theorem range_perfectSupportedKMap_eq_ker_perfectOpenKMap (n : ℕ) :
    (perfectSupportedKMap j n).range = (perfectOpenKMap j n).ker := by
  have h := range_acyclicInclusion_eq_ker_changeWeak_of_weak (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n
  rw [← perfectAcyclicSupportedKEquiv_inclusion j n] at h
  unfold perfectOpenKMap
  rw [← h]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(perfectAcyclicSupportedKEquiv j n).symm a, by simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨perfectAcyclicSupportedKEquiv j n a, rfl⟩

/-- Exactness at the existing supported K-group. -/
theorem range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap (n : ℕ) :
    (perfectOpenConnectingHom j n).range = (perfectSupportedKMap j n).ker := by
  have h := range_changeWeakConnectingHom_eq_ker_acyclicInclusion (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    change perfectSupportedKMap j n (perfectOpenConnectingHom j n b) = 1
    change (perfectSupportedKMap j n).comp
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom
      (changeWeakConnectingHom (perfectOpenNested j)
        (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n b) = 1
    rw [perfectAcyclicSupportedKEquiv_inclusion]
    have hm : changeWeakConnectingHom (perfectOpenNested j)
        (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n b ∈
        (changeWeakConnectingHom (perfectOpenNested j)
          (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n).range := ⟨b, rfl⟩
    rw [h] at hm
    exact hm
  · intro ha
    have hm : (perfectAcyclicSupportedKEquiv j n).symm a ∈
        (KMap (acyclicInclusion_exact (perfectOpenNested j)) n).ker := by
      change KMap (acyclicInclusion_exact (perfectOpenNested j)) n
        ((perfectAcyclicSupportedKEquiv j n).symm a) = 1
      exact (DFunLike.congr_fun (perfectAcyclicSupportedKEquiv_symm_inclusion j n) a).trans ha
    rw [← h] at hm
    obtain ⟨b, hb⟩ := hm
    refine ⟨b, ?_⟩
    change perfectAcyclicSupportedKEquiv j n _ = a
    exact (congrArg (perfectAcyclicSupportedKEquiv j n) hb).trans
      ((perfectAcyclicSupportedKEquiv j n).apply_symm_apply a)

/-- Exactness at the named relative coarse K-group. -/
theorem range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom (n : ℕ) :
    (perfectOpenKMap j (n + 1)).range = (perfectOpenConnectingHom j n).ker := by
  have h := range_changeWeak_eq_ker_changeWeakConnectingHom (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n
  change (KMap (changeWeak_exact (perfectOpenNested j)) (n + 1)).range = _
  rw [h]
  ext a
  change _ = 1 ↔ perfectAcyclicSupportedKEquiv j n _ = 1
  exact (map_eq_one_iff (perfectAcyclicSupportedKEquiv j n)
    (perfectAcyclicSupportedKEquiv j n).injective).symm

/-- All recurring positions of the genuine original relative-open sequence. -/
@[colib_tag "COL-0300"]
theorem perfectOpen_positiveLongExactSequence (n : ℕ) :
    (perfectOpenKMap j (n + 1)).range = (perfectOpenConnectingHom j n).ker ∧
    (perfectOpenConnectingHom j n).range = (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range = (perfectOpenKMap j n).ker :=
  ⟨range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom j n,
    range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap j n,
    range_perfectSupportedKMap_eq_ker_perfectOpenKMap j n⟩

/-- Degree zero surjects onto the relative model, not onto perfect K-theory of the open. -/
@[colib_tag "COL-0300"]
theorem perfectOpenKMap_zero_surjective : Function.Surjective (perfectOpenKMap j 0) :=
  changeWeak_KMap_zero_surjective_of_weak (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)

end AlgebraicGeometry.Scheme.Modules
