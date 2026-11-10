/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopyInvariance
public import Colib.Topology.LocalCoefficients.UniverseLift
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Cancellation for an actual displayed homotopy factorization

Both the comparison map and its homotopy are supplied. The proof uses the
existing coefficient-corrected homology formulas and cancels actual isomorphisms.
It does not construct a factorization or an inverse map. The UniverseLift
conclusion retains the original arbitrary-universe API specialized to one
common space and coefficient universe.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A displayed homotopy factorization cancels a known original homology
isomorphism, with both mandatory coefficient transports retained. -/
theorem isIso_pushforwardHomologyMap_of_displayed_factorization
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    (A : System.{u, u} Z) (n : ℕ)
    (hf : IsIso (pushforwardHomologyMap f (pullback k A) n))
    (hg : IsIso (pushforwardHomologyMap g A n)) :
    IsIso (pushforwardHomologyMap k A n) := by
  have hcomp := (isIso_pushforwardHomologyMap_iff_of_homotopy H A n).mpr hg
  rw [pushforwardHomologyMap_comp] at hcomp
  change IsIso ((coefficientHomologyIso (pullbackCompositionIso f k A) n).hom ≫
    pushforwardHomologyMap f (pullback k A) n ≫ pushforwardHomologyMap k A n) at hcomp
  let := hf
  exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hcomp)

/-- The supplied comparison has quasi-isomorphic original twisted chains
when its actual homotopy factorization has two such original maps. -/
theorem universeLift_quasiIso_of_displayed_factorization
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    (A : System.{u, u} Z)
    (hf : QuasiIso (UniverseLift.chainMap.{u, u, u} f (pullback k A)))
    (hg : QuasiIso (UniverseLift.chainMap.{u, u, u} g A)) :
    QuasiIso (UniverseLift.chainMap.{u, u, u} k A) := by
  let := hf
  let := hg
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
  change IsIso (UniverseLift.homologyMap k A n)
  apply (UniverseLift.isIso_homologyMap_iff k A n).mpr
  apply isIso_pushforwardHomologyMap_of_displayed_factorization f g k H A n
  · apply (UniverseLift.isIso_homologyMap_iff f (pullback k A) n).mp
    change IsIso (HomologicalComplex.homologyMap
      (UniverseLift.chainMap f (pullback k A)) n)
    infer_instance
  · apply (UniverseLift.isIso_homologyMap_iff g A n).mp
    change IsIso (HomologicalComplex.homologyMap (UniverseLift.chainMap g A) n)
    infer_instance


attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/MapCancellation.lean:35-46"
  "adaptation" "Original displayed homotopy and both coefficient transports in one common universe"]
  isIso_pushforwardHomologyMap_of_displayed_factorization

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/MapCancellation.lean:50-70"
  "adaptation" "Original displayed homotopy and both coefficient transports in one common universe"]
  universeLift_quasiIso_of_displayed_factorization

end FundamentalGroupoid.LocalCoefficients
