/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Colib.Topology.Prespectrum.HomotopyTransport
import Colib.Topology.Prespectrum.ConeStableNaturality
import Colib.Topology.Prespectrum.ConeDescZeroComparison
import Colib.KTheory.Waldhausen.Iterated.ConeStableSequence

/-!
Regressions for endpoint-only homotopy casts, the original signed cone boundary and the
canonical cokernel inclusion. Generic excision and vanishing assumptions remain explicit;
actual S-model cone exactness discharges excision using its already proved native theorem.
-/

open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

universe u v

noncomputable section

section HomotopyTransport

variable {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
  (H : Homotopy f g) (hf : f = f') (hg : g = g')

example (n : ℕ) : (H.cast hf hg).level n = H.level n := Homotopy.cast_level H hf hg n

example (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.cast hf hg).level n (s, x) = H.level n (s, x) := rfl

example {K : Homotopy f g} (J : H.RelHomotopy K) (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    (J.cast hf hg).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl

end HomotopyTransport

section Naturality

variable {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
  (hA : IsStableEquivalence (mappingConeFiberComparison A.hom))
  (hB : IsStableEquivalence (mappingConeFiberComparison B.hom))

example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeMap sq) ≫
      stableMappingConeConnecting B.hom hB d =
        stableMappingConeConnecting A.hom hA d ≫ (stableHomotopyFunctor d).map sq.left :=
  stableMappingConeConnecting_naturality sq hA hB d

example (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_excision sq hA hB hl hr

end Naturality

section Cokernel

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f))

example [Subsingleton (stableHomotopyGroup E (-1))] :
    cokernel.π ((stableHomotopyFunctor 0).map f) ≫
      (stableMappingConeZeroCokernelIso f hf).hom =
        (stableHomotopyFunctor 0).map (mappingConeInclusion f) :=
  stableMappingConeZeroCokernelIso_π f hf

example (d : ℤ) [Subsingleton (stableHomotopyGroup E (d - 1))] :
    cokernel.π ((stableHomotopyFunctor d).map f) ≫
      (stableMappingConeDegreeCokernelIso f hf d).hom =
        (stableHomotopyFunctor d).map (mappingConeInclusion f) :=
  stableMappingConeDegreeCokernelIso_π f hf d

example {G : LoopPrespectrum.{u}} (g : F ⟶ G)
    (N : Homotopy (f ≫ g) (zeroHom E G))
    [Subsingleton (stableHomotopyGroup E (-1))]
    (he : Function.Exact ((stableHomotopyFunctor 0).map f)
      ((stableHomotopyFunctor 0).map g))
    (hg : Function.Surjective ((stableHomotopyFunctor 0).map g)) :
    Function.Bijective ((stableHomotopyFunctor 0).map (mappingConeDesc f g N)) :=
  mappingConeDesc_stable_zero_bijective f g N hf he hg

end Cokernel

example {W V W' V' : WideSubcategory preservesZero.{u}}
    {f : prespectrum W ⟶ prespectrum V} {g : prespectrum W' ⟶ prespectrum V'}
    (sq : Arrow.mk f ⟶ Arrow.mk g)
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) :=
  prespectrum_mappingConeMap_isStableEquivalence sq hl hr

example {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V)
    (d : ℤ) : Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  originalPrespectrum_stableMappingCone_exact_target W V f d

example {W V : WideSubcategory preservesZero.{u}}
    (f : prespectrum W ⟶ prespectrum V) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f))
      (stableMappingConeConnecting f
        (prespectrum_mappingConeFiberComparison_isStableEquivalence f) d) ∧
    Function.Exact (stableMappingConeConnecting f
      (prespectrum_mappingConeFiberComparison_isStableEquivalence f) d)
      ((stableHomotopyFunctor d).map f) ∧
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  prespectrum_stableMappingConeLongExactSequence f d
