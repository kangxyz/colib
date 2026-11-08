/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-!
# The original supported inclusion in the relative-open long exact sequence

The genuine relative-coarse fibration and explicit exact supported equivalence
give all three positions of the connective long exact sequence. The inclusion
is literally the existing `perfectSupportedUnionKMap`; the target is the named
`PerfectSupportedOpenCoarseK`, not `PerfectK U`. In particular relative degree-zero
surjectivity below makes no surjectivity claim for open restriction.
-/
@[expose] public section

open CategoryTheory.Waldhausen


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The genuine homotopy-fiber boundary in the original supported K-groups. -/
def perfectSupportedOpenConnectingHom (n : ℕ) : PerfectSupportedOpenCoarseK j T (n + 1) →*
  PerfectSupportedK (T ⊔ j.opensRange).ι n :=
  (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom.comp
    (changeWeakConnectingHom (perfectSupportedOpenNested j T)
      (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n)

/-- The original supported K-groups map to the actual canonical homotopy fiber. -/
def perfectSupportedUnionFiberKMap (n : ℕ) : PerfectSupportedK (T ⊔ j.opensRange).ι n →*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (changeWeakMap (perfectSupportedOpenNested j T))
        (perfectSupportedOpenWeakWaldhausen j T).kBasepoint)
      (HomotopyFiber.basepoint (changeWeakMap (perfectSupportedOpenNested j T))
        (perfectSupportedOpenWeakWaldhausen j T).kBasepoint (perfectSupportedWaldhausen
          T.ι).kBasepoint
        (changeWeakMap_basepoint (perfectSupportedOpenNested j T))) :=
  (canonicalFiberKMap (perfectSupportedOpenNested j T) n).comp
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom

/-- The supported-to-fiber map is bijective in every connective K-degree. -/
theorem perfectSupportedUnionFiberKMap_bijective (n : ℕ) :
    Function.Bijective (perfectSupportedUnionFiberKMap j T n) :=
  (canonicalFiberKMap_bijective_of_weak (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n).comp
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.bijective

/-- Projection of the actual fiber map is precisely the existing supported inclusion. -/
theorem perfectSupportedUnionFiberKMap_projection (n : ℕ) :
    (HomotopyGroup.piMap n
      (HomotopyFiber.projection (changeWeakMap (perfectSupportedOpenNested j T))
      (perfectSupportedOpenWeakWaldhausen j T).kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ (perfectSupportedWaldhausen T.ι).kBasepoint
        (changeWeakMap_basepoint (perfectSupportedOpenNested j T)))).comp
      (perfectSupportedUnionFiberKMap j T n) = perfectSupportedUnionKMap j T n := by
  rw [perfectSupportedUnionFiberKMap, ← MonoidHom.comp_assoc]
  erw [canonicalFiberKMap_projection]
  exact perfectSupportedOpenAcyclicSupportedKEquiv_symm_inclusion j T n

/-- The transported boundary has the original full canonical homotopy-fiber boundary. -/
theorem perfectSupportedUnionFiberKMap_connecting (n : ℕ)
    (a : PerfectSupportedOpenCoarseK j T (n + 1)) :
    perfectSupportedUnionFiberKMap j T n (perfectSupportedOpenConnectingHom j T n a) =
      HomotopyFiber.connectingHom (changeWeakMap (perfectSupportedOpenNested j T))
        (perfectSupportedOpenWeakWaldhausen j T).kBasepoint (perfectSupportedWaldhausen
          T.ι).kBasepoint
        (changeWeakMap_basepoint (perfectSupportedOpenNested j T)) n a := by
  change canonicalFiberKMap (perfectSupportedOpenNested j T) n
    ((perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm
      (perfectSupportedOpenAcyclicSupportedKEquiv j T n
        (changeWeakConnectingHom (perfectSupportedOpenNested j T)
          (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n a))) = _
  rw [MulEquiv.symm_apply_apply]
  exact canonicalFiberKMap_connecting (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n a

/-- Exactness at the original perfect K-group, with its existing supported inclusion. -/
theorem range_perfectSupportedUnionKMap_eq_ker_perfectSupportedOpenKMap (n : ℕ) :
    (perfectSupportedUnionKMap j T n).range = (perfectSupportedOpenKMap j T n).ker := by
  have h := range_acyclicInclusion_eq_ker_changeWeak_of_weak (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n
  rw [← perfectSupportedOpenAcyclicSupportedKEquiv_inclusion j T n] at h
  unfold perfectSupportedOpenKMap
  rw [← h]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm a, by simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨perfectSupportedOpenAcyclicSupportedKEquiv j T n a, rfl⟩

/-- Exactness at the existing supported K-group. -/
theorem range_perfectSupportedOpenConnectingHom_eq_ker_perfectSupportedUnionKMap (n : ℕ) :
    (perfectSupportedOpenConnectingHom j T n).range = (perfectSupportedUnionKMap j T n).ker := by
  have h := range_changeWeakConnectingHom_eq_ker_acyclicInclusion (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    change perfectSupportedUnionKMap j T n (perfectSupportedOpenConnectingHom j T n b) = 1
    change (perfectSupportedUnionKMap j T n).comp
      (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom
      (changeWeakConnectingHom (perfectSupportedOpenNested j T)
        (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n b) = 1
    rw [perfectSupportedOpenAcyclicSupportedKEquiv_inclusion]
    have hm : changeWeakConnectingHom (perfectSupportedOpenNested j T)
        (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n b ∈
        (changeWeakConnectingHom (perfectSupportedOpenNested j T)
          (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n).range := ⟨b,
            rfl⟩
    rw [h] at hm
    exact hm
  · intro ha
    have hm : (perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm a ∈
        (KMap (acyclicInclusion_exact (perfectSupportedOpenNested j T)) n).ker := by
      change KMap (acyclicInclusion_exact (perfectSupportedOpenNested j T)) n
        ((perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm a) = 1
      exact (DFunLike.congr_fun (perfectSupportedOpenAcyclicSupportedKEquiv_symm_inclusion j T n)
        a).trans ha
    rw [← h] at hm
    obtain ⟨b, hb⟩ := hm
    refine ⟨b, ?_⟩
    change perfectSupportedOpenAcyclicSupportedKEquiv j T n _ = a
    exact (congrArg (perfectSupportedOpenAcyclicSupportedKEquiv j T n) hb).trans
      ((perfectSupportedOpenAcyclicSupportedKEquiv j T n).apply_symm_apply a)

/-- Exactness at the named relative coarse K-group. -/
theorem range_perfectSupportedOpenKMap_eq_ker_perfectSupportedOpenConnectingHom (n : ℕ) :
    (perfectSupportedOpenKMap j T (n + 1)).range = (perfectSupportedOpenConnectingHom j T n).ker :=
      by
  have h := range_changeWeak_eq_ker_changeWeakConnectingHom (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n
  change (KMap (changeWeak_exact (perfectSupportedOpenNested j T)) (n + 1)).range = _
  rw [h]
  ext a
  change _ = 1 ↔ perfectSupportedOpenAcyclicSupportedKEquiv j T n _ = 1
  exact (map_eq_one_iff (perfectSupportedOpenAcyclicSupportedKEquiv j T n)
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).injective).symm

/-- All recurring positions of the genuine original relative-open sequence. -/
theorem perfectSupportedOpen_positiveLongExactSequence (n : ℕ) :
    (perfectSupportedOpenKMap j T (n + 1)).range = (perfectSupportedOpenConnectingHom j T n).ker ∧
    (perfectSupportedOpenConnectingHom j T n).range = (perfectSupportedUnionKMap j T n).ker ∧
    (perfectSupportedUnionKMap j T n).range = (perfectSupportedOpenKMap j T n).ker :=
  ⟨range_perfectSupportedOpenKMap_eq_ker_perfectSupportedOpenConnectingHom j T n,
    range_perfectSupportedOpenConnectingHom_eq_ker_perfectSupportedUnionKMap j T n,
    range_perfectSupportedUnionKMap_eq_ker_perfectSupportedOpenKMap j T n⟩

/-- Degree zero surjects onto the relative model, not onto perfect K-theory of the open. -/
theorem perfectSupportedOpenKMap_zero_surjective : Function.Surjective (perfectSupportedOpenKMap j T
  0) :=
  changeWeak_KMap_zero_surjective_of_weak (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)

/-- The three recurring positions include the degree-zero supported group. -/
theorem perfectSupportedOpen_zeroLongExactSequence :
    (perfectSupportedOpenKMap j T 1).range = (perfectSupportedOpenConnectingHom j T 0).ker ∧
    (perfectSupportedOpenConnectingHom j T 0).range = (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedOpenKMap j T 0).ker :=
  perfectSupportedOpen_positiveLongExactSequence j T 0

/-- The honest relative K₀ tail ends at the coarse model, not at the fine open group. -/
theorem perfectSupportedOpen_relativeKZeroTail :
    (perfectSupportedOpenConnectingHom j T 0).range = (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedOpenKMap j T 0).ker ∧
    Function.Surjective (perfectSupportedOpenKMap j T 0) :=
  ⟨range_perfectSupportedOpenConnectingHom_eq_ker_perfectSupportedUnionKMap j T 0,
    range_perfectSupportedUnionKMap_eq_ker_perfectSupportedOpenKMap j T 0,
    perfectSupportedOpenKMap_zero_surjective j T⟩

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0331",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/LongExactSequence.lean:34-163"
    "adaptation"
    "Native supported relative-open coarse model and actual maps, without fine-open comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedUnionFiberKMap
  AlgebraicGeometry.Scheme.Modules.perfectSupportedUnionFiberKMap_projection
  AlgebraicGeometry.Scheme.Modules.perfectSupportedUnionFiberKMap_connecting
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpen_positiveLongExactSequence
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpen_zeroLongExactSequence
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpen_relativeKZeroTail
