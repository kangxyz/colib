/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenForgetPrespectrum
public import Colib.KTheory.Waldhausen.Fibration.StableConnectingComparison

/-!
# Auxiliary-support forgetting and the signed stable boundary

The signed intrinsic boundaries of the actual supported fiber lifts commute in every integer
degree. Only the two original fiber lifts are inverted; support forgetting is not assumed to be
a stable equivalence. In connective degrees the stable boundary is the negative of the original
K-theory boundary, with its explicit degree cast, including K₁ to K₀.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The actual supported lift, rather than a forgetting map, is invertible stably. -/
theorem perfectSupportedUnionFiberLift_isIso (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
        (perfectSupportedUnionInclusionPrespectrumMap j T)
        (perfectSupportedUnionPrespectrumNullhomotopy j T))) := by
  rw [← perfectSupportedUnionFiberPrespectrumMap_eq_lift]
  exact perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence j T d

/-- The ordinary original supported lift is also invertible stably. -/
theorem perfectSupportedFiberLift_isIso (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
        (perfectSupportedInclusionPrespectrumMap j)
        (perfectSupportedPrespectrumNullhomotopy j))) := by
  rw [← perfectSupportedFiberPrespectrumMap_eq_lift]
  exact perfectSupportedFiberPrespectrumMap_isStableEquivalence j d

/-- The original signed intrinsic stable boundary of the supported localization fiber. -/
def perfectSupportedOpenStableConnecting (d : ℤ) :
    stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) (d + 1) ⟶
      stableHomotopyGroup (perfectSupportedUnionPrespectrum j T) d :=
  let := perfectSupportedUnionFiberLift_isIso j T d
  stableFiberLiftConnecting (perfectSupportedUnionInclusionPrespectrumMap j T)
    (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
    (perfectSupportedUnionPrespectrumNullhomotopy j T) d

/-- The corresponding original signed intrinsic boundary without auxiliary support. -/
def perfectOpenStableConnecting (d : ℤ) :
    stableHomotopyGroup (perfectOpenPrespectrum j) (d + 1) ⟶
      stableHomotopyGroup (perfectSupportedPrespectrum j) d :=
  let := perfectSupportedFiberLift_isIso j d
  stableFiberLiftConnecting (perfectSupportedInclusionPrespectrumMap j)
    (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
    (perfectSupportedPrespectrumNullhomotopy j) d

/-- Whole-null naturality implies the original signed boundary square in every integer degree. -/
theorem perfectSupportedOpenStableConnecting_forget (d : ℤ) :
    perfectSupportedOpenStableConnecting j T d ≫
        (stableHomotopyFunctor d).map (perfectSupportedUnionForgetPrespectrumMap j T) =
      (stableHomotopyFunctor (d + 1)).map (perfectSupportedOpenForgetPrespectrumMap j T) ≫
        perfectOpenStableConnecting j d := by
  let := perfectSupportedUnionFiberLift_isIso j T d
  let := perfectSupportedFiberLift_isIso j d
  exact stableFiberLiftConnecting_naturality
    (perfectSupportedUnionInclusionPrespectrumMap j T)
    (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
    (perfectSupportedInclusionPrespectrumMap j)
    (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
    (perfectSupportedUnionPrespectrumNullhomotopy j T)
    (perfectSupportedPrespectrumNullhomotopy j)
    (perfectSupportedUnionForgetPrespectrumMap j T)
    (perfectSupportedInclusionPrespectrumMap T.ι)
    (perfectSupportedOpenForgetPrespectrumMap j T)
    (perfectSupportedUnionForgetPrespectrumMap_inclusion j T)
    (perfectSupportedOpenForgetPrespectrumMap_changeWeak j T).symm
    (perfectSupportedUnionPrespectrumNullhomotopy_forget j T) d

/-- The union-supported fiber image of the original K-boundary retains the minus sign. -/
theorem perfectSupportedUnionFiberPrespectrumMap_connecting_sign (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : PerfectSupportedOpenCoarseK j T (n + 1)) :
    stableFiberConnecting
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T)) κ)
          (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) (n + 1)
            (Additive.ofMul a))) =
      -((stableHomotopyFunctor (n : ℤ)).map (perfectSupportedUnionFiberPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
          (Additive.ofMul (perfectSupportedOpenConnectingHom j T n a)))) := by
  have h := originalKStableEquiv_naturality
    (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
    (perfectSupportedUnionToAcyclic_exact j T) rfl n
    (perfectSupportedOpenConnectingHom j T n a)
  have hK : KMap (perfectSupportedUnionToAcyclic_exact j T) n
      (perfectSupportedOpenConnectingHom j T n a) =
        Fibration.changeWeakConnectingHom (perfectSupportedOpenNested j T)
          (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n a :=
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm_apply_apply _
  rw [hK] at h
  rw [perfectSupportedUnionFiberPrespectrumMap, Functor.map_comp]
  exact (Fibration.originalKStableEquiv_connecting_sign (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n κ a).trans
      (congrArg (fun b ↦ -((stableHomotopyFunctor (n : ℤ)).map
        (Fibration.canonicalFiberPrespectrumMap (perfectSupportedOpenNested j T)) b)) h)

/-- The ordinary supported fiber image has the same original boundary sign. -/
theorem perfectSupportedFiberPrespectrumMap_connecting_sign (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : PerfectOpenK j (n + 1)) :
    stableFiberConnecting (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectOpenPrespectrum j)) κ)
          (originalKStableEquiv (perfectOpenWeakWaldhausen j) (n + 1) (Additive.ofMul a))) =
      -((stableHomotopyFunctor (n : ℤ)).map (perfectSupportedFiberPrespectrumMap j)
        (originalKStableEquiv (perfectSupportedWaldhausen j) n
          (Additive.ofMul (perfectOpenConnectingHom j n a)))) := by
  have h := originalKStableEquiv_naturality (perfectSupportedWaldhausen j)
    (Fibration.acyclicStructure (perfectOpenNested j)) (perfectSupportedToAcyclic_exact j)
    rfl n (perfectOpenConnectingHom j n a)
  have hK : KMap (perfectSupportedToAcyclic_exact j) n (perfectOpenConnectingHom j n a) =
      Fibration.changeWeakConnectingHom (perfectOpenNested j)
        (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n a :=
    (perfectAcyclicSupportedKEquiv j n).symm_apply_apply _
  rw [hK] at h
  rw [perfectSupportedFiberPrespectrumMap, Functor.map_comp]
  exact (Fibration.originalKStableEquiv_connecting_sign (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n κ a).trans
      (congrArg (fun b ↦ -((stableHomotopyFunctor (n : ℤ)).map
        (Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j)) b)) h)

/-- Intrinsic supported stable boundary agrees with the negative original K-boundary. -/
theorem perfectSupportedOpenStableConnecting_sign (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : PerfectSupportedOpenCoarseK j T (n + 1)) :
    perfectSupportedOpenStableConnecting j T (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T)) κ)
          (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) (n + 1)
            (Additive.ofMul a))) =
      -(originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
        (Additive.ofMul (perfectSupportedOpenConnectingHom j T n a))) := by
  let := perfectSupportedUnionFiberLift_isIso j T (n : ℤ)
  let := perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence j T (n : ℤ)
  apply (ConcreteCategory.bijective_of_isIso
    ((stableHomotopyFunctor (n : ℤ)).map
      (perfectSupportedUnionFiberPrespectrumMap j T))).injective
  have h := ConcreteCategory.congr_hom (stableFiberLiftConnecting_comp_lift
    (perfectSupportedUnionInclusionPrespectrumMap j T)
    (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
    (perfectSupportedUnionPrespectrumNullhomotopy j T) (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T)) κ)
      (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) (n + 1) (Additive.ofMul a)))
  rw [← perfectSupportedUnionFiberPrespectrumMap_eq_lift] at h
  exact h.trans ((perfectSupportedUnionFiberPrespectrumMap_connecting_sign j T n κ a).trans
    (map_neg _ _).symm)

/-- Intrinsic ordinary stable boundary agrees with the negative original K-boundary. -/
theorem perfectOpenStableConnecting_sign (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : PerfectOpenK j (n + 1)) :
    perfectOpenStableConnecting j (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectOpenPrespectrum j)) κ)
          (originalKStableEquiv (perfectOpenWeakWaldhausen j) (n + 1) (Additive.ofMul a))) =
      -(originalKStableEquiv (perfectSupportedWaldhausen j) n
        (Additive.ofMul (perfectOpenConnectingHom j n a))) := by
  let := perfectSupportedFiberLift_isIso j (n : ℤ)
  let := perfectSupportedFiberPrespectrumMap_isStableEquivalence j (n : ℤ)
  apply (ConcreteCategory.bijective_of_isIso
    ((stableHomotopyFunctor (n : ℤ)).map (perfectSupportedFiberPrespectrumMap j))).injective
  have h := ConcreteCategory.congr_hom (stableFiberLiftConnecting_comp_lift
    (perfectSupportedInclusionPrespectrumMap j)
    (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
    (perfectSupportedPrespectrumNullhomotopy j) (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup (perfectOpenPrespectrum j)) κ)
      (originalKStableEquiv (perfectOpenWeakWaldhausen j) (n + 1) (Additive.ofMul a)))
  rw [← perfectSupportedFiberPrespectrumMap_eq_lift] at h
  exact h.trans ((perfectSupportedFiberPrespectrumMap_connecting_sign j n κ a).trans
    (map_neg _ _).symm)

attribute [colib_tag "COL-0337",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/StableConnectingComparison.lean"
    "comparison" "The support-forgetting square retains the original signed stable boundary"]
  perfectSupportedOpenStableConnecting_forget
  perfectSupportedUnionFiberPrespectrumMap_connecting_sign
  perfectSupportedFiberPrespectrumMap_connecting_sign
  perfectSupportedOpenStableConnecting_sign
  perfectOpenStableConnecting_sign

end AlgebraicGeometry.Scheme.Modules
