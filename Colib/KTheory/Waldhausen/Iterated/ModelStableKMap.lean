/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison
public import Colib.Topology.Prespectrum.StableLevelOne

/-! # Actual Model K-map transport and negative stable groups

Only the three original transfer/vanishing statements missing from the native direct Model API
are selected. The unchanged level-one naturality is the existing smallModelKStableEquiv_naturality,
whose stable equivalence has exactly the same definition. No alternate small model is introduced.
-/
@[expose] public noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- Injectivity of the unchanged K-map gives injectivity of the actual nonnegative stable map. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/StableKMap.lean:39"
  "adaptation" "Original direct Model stable transfer; reuse native level-one naturality"]
theorem prespectrumMap_stable_nonnegative_injective {W V : WideSubcategory preservesZero.{u}} (f :
  W ⟶ V)
    (n : ℕ) (hf : Function.Injective (KMap f.hom.isExact n)) :
    Function.Injective ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) := by
  let eW := levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) n
  let eV := levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) n
  intro x y hxy
  obtain ⟨a, rfl⟩ := eW.surjective x
  obtain ⟨b, rfl⟩ := eW.surjective y
  have h := (smallModelKStableEquiv_naturality f n a.toMul).trans
    (hxy.trans (smallModelKStableEquiv_naturality f n b.toMul).symm)
  have hab := hf (congrArg Additive.toMul (eV.injective h))
  exact congrArg eW (congrArg Additive.ofMul hab)

/-- Surjectivity transports through the same original K-to-stable comparison. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/StableKMap.lean:53"
  "adaptation" "Original direct Model stable transfer; reuse native level-one naturality"]
theorem prespectrumMap_stable_nonnegative_surjective {W V : WideSubcategory preservesZero.{u}} (f
  : W ⟶ V)
    (n : ℕ) (hf : Function.Surjective (KMap f.hom.isExact n)) :
    Function.Surjective ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) := by
  let eW := levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) n
  let eV := levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) n
  intro y
  obtain ⟨b, rfl⟩ := eV.surjective y
  obtain ⟨a, ha⟩ := hf b.toMul
  exact ⟨eW (Additive.ofMul a),
    (smallModelKStableEquiv_naturality f n a).symm.trans
      (congrArg eV (congrArg Additive.ofMul ha))⟩

/-- Connectivity of the actual positive Model levels gives all negative stable vanishing. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/StableKMap.lean:66"
  "adaptation" "Original direct Model stable transfer; reuse native level-one naturality"]
theorem prespectrum_stableHomotopyGroup_neg_subsingleton (W : WideSubcategory preservesZero.{u})
    (d : ℤ) (hd : d < 0) : Subsingleton (stableHomotopyGroup (prespectrum W) d) :=
  stableHomotopyGroup_subsingleton_of_neg (prespectrum W) (prespectrum_isOmega W)
    (fun n ↦ stageSpace_pathConnected n W) d hd

end CategoryTheory.Waldhausen.IteratedS
