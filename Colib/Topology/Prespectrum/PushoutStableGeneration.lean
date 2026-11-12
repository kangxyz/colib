/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.PushoutConeCollapse
public import Colib.Topology.Prespectrum.ConeStableExactness

/-!
Source: `Quillen/Topology/Prespectrum/PushoutStableGeneration.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Stable generation by the original reduced-pushout inclusions

The actual right-cone collapse and genuine cone sequences show that the two unchanged inclusions
jointly generate a signed stable group whenever the overlap's preceding group vanishes. The
generic statement records actual row excision and stability of the original collapse explicitly.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The literal left inclusion is retained by the original right-inclusion cone collapse. -/
theorem inl_coneInclusion_rightConeCollapse :
    inl f g ≫ mappingConeInclusion (inr f g) ≫ rightConeCollapse f g =
      mappingConeInclusion f := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The two original inclusions generate when the overlap's preceding signed group is zero. -/
theorem stable_inclusions_generate
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hcollapse : IsStableEquivalence (rightConeCollapse f g))
    (d : ℤ) (hA : Subsingleton (stableHomotopyGroup A (d - 1)))
    (z : stableHomotopyGroup (prespectrum f g) d) :
    ∃ b : stableHomotopyGroup B d, ∃ c : stableHomotopyGroup C d,
      (stableHomotopyFunctor d).map (inl f g) b +
        (stableHomotopyFunctor d).map (inr f g) c = z := by
  let := hcollapse d
  have hincl : Function.Surjective ((stableHomotopyFunctor d).map (mappingConeInclusion f)) := by
    have hs (e : ℤ) (he : e = d - 1 + 1) : Function.Surjective
        ((stableHomotopyFunctor e).map (mappingConeInclusion f)) := by
      subst e
      intro y
      exact (stableMappingConeConnecting_exact_cone f hf (d - 1) y).mp (hA.elim _ _)
    exact hs d (by omega)
  obtain ⟨b, hb⟩ := hincl ((stableHomotopyFunctor d).map (rightConeCollapse f g)
    ((stableHomotopyFunctor d).map (mappingConeInclusion (inr f g)) z))
  have hleft := ConcreteCategory.congr_hom
    (congrArg (fun k => (stableHomotopyFunctor d).map k)
      (inl_coneInclusion_rightConeCollapse f g)) b
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hleft
  let lb : stableHomotopyGroup (prespectrum f g) d :=
    (stableHomotopyFunctor d).map (inl f g) b
  have hz : (stableHomotopyFunctor d).map (mappingConeInclusion (inr f g))
      (z - lb) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor d).map (rightConeCollapse f g))).injective
    simp only [map_sub, map_zero, lb, hleft, hb, sub_self]
  obtain ⟨c, hc⟩ := (stableMappingCone_exact_target (inr f g) hi d _).mp hz
  refine ⟨b, c, ?_⟩
  rw [hc]
  change lb + (z - lb) = z
  abel

/-- Vanishing of the actual three relevant corner groups forces vanishing of the pushout group. -/
theorem stableHomotopyGroup_subsingleton_of_corner_groups
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hcollapse : IsStableEquivalence (rightConeCollapse f g))
    (d : ℤ) (hA : Subsingleton (stableHomotopyGroup A (d - 1)))
    (hB : Subsingleton (stableHomotopyGroup B d))
    (hC : Subsingleton (stableHomotopyGroup C d)) :
    Subsingleton (stableHomotopyGroup (prespectrum f g) d) := by
  have hz (z : stableHomotopyGroup (prespectrum f g) d) : z = 0 := by
    obtain ⟨b, c, h⟩ := stable_inclusions_generate f g hf hi hcollapse d hA z
    rw [hB.elim b 0, hC.elim c 0, map_zero, map_zero, zero_add] at h
    exact h.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Topology.LoopPrespectrum.HomotopyPushout
