/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.Connectivity
public import Colib.Topology.DoubleMappingCylinder.PlusGapConnectivity
public import Colib.Topology.HomotopyPullback.PiOneKernel
public import Colib.Topology.HomotopyPullback.Symmetry
public import Colib.Topology.HomotopyPullback.ConnectivityReflection

/-!
# Fundamental groups of the original double-cylinder legs

The genuine degree-one excision range gives the gap surjection. Actual fiber
coordinates and the pointwise unit-path correction then give injectivity of
each leg from the corresponding kernel inclusion. Surjectivity is derived
from the actual pullback projection and its fiber equivalence. Thus two
surjections with equal original kernels make both original legs Pi-one
isomorphisms. No fundamental-group pushout or leg isomorphism is assumed.
-/

/-! Adapted from `Quillen/Topology/DoubleMappingCylinder/PiOneLegs.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory Topology
universe u w

namespace Topology.HomotopyPullback
variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

/-- A surjective original pullback projection gives surjectivity of the original
map using the actual parameter-fiber equivalence and connected target paths. -/
theorem piOne_surjective_of_baseProjection_surjective (f : C(X, B)) (g : C(A, B))
    [PathConnectedSpace A] [PathConnectedSpace B] [PathConnectedSpace (HomotopyPullback f g)]
    (z : HomotopyPullback f g)
    (hq : Function.Surjective (HomotopyGroup.piMap 0 (baseProjection f g) (x := z) rfl)) :
    Function.Surjective (HomotopyGroup.piMap 0 f (x := sourceProjection f g z) rfl) := by
  have hproj := isHomotopyConnectedMap_one_of_piOne_surjective (baseProjection f g) z hq
  have h := isHomotopyConnectedMap_of_baseProjection f g (baseProjection f g z) 1 hproj
  exact h.homotopyGroupMap_surjective (sourceProjection f g z) 1 (by omega)

end Topology.HomotopyPullback

namespace TopCat.DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

include sq

/-- Equal kernels of the two original surjections make the original left leg
bijective on Pi one, via the genuine degree-one gap and actual fiber chase. -/
theorem leftEnd_piOne_bijective_of_equal_kernel
    [PathConnectedSpace A] [PathConnectedSpace B] [PathConnectedSpace C]
    (a : A) (hf : Function.Surjective (HomotopyGroup.piMap 0 f.hom (x := a) rfl))
    (hg : Function.Surjective (HomotopyGroup.piMap 0 g.hom (x := a) rfl))
    (hker : (HomotopyGroup.piMap 0 f.hom (x := a) rfl).ker =
      (HomotopyGroup.piMap 0 g.hom (x := a) rfl).ker) :
    Function.Bijective (HomotopyGroup.piMap 0 (gapLeftEndpoint e) (x := f a) rfl) := by
  let := pathConnectedSpace f g sq a
  have hgap := gap_isHomotopyConnectedMap f g sq 1 1 1 (by omega)
    (isHomotopyConnectedMap_one_of_piOne_surjective f.hom a hf)
    (isHomotopyConnectedMap_one_of_piOne_surjective g.hom a hg)
  let := subsingleton_homotopyGroup_zero a
  let := pathConnectedSpace_of_subsingleton_pi_zero (gap f g sq a)
    ((hgap.homotopyGroupMap_zero_surjective a).subsingleton)
  refine ⟨?_, ?_⟩
  · exact HomotopyPullback.piOne_injective_of_gap_surjective
      (gapLeftEndpoint e) (gapRightEndpoint e) (gap f g sq) a
      (hgap.homotopyGroupMap_surjective a 1 (by omega)) hker.symm.le
  · apply HomotopyPullback.piOne_surjective_of_baseProjection_surjective
      (gapLeftEndpoint e) (gapRightEndpoint e) (gap f g sq a)
    intro b
    obtain ⟨c, hc⟩ := hg b
    refine ⟨HomotopyGroup.piMap 0 (gap f g sq) rfl c, ?_⟩
    change HomotopyGroup.map (N := Fin 1) _ rfl (HomotopyGroup.map _ rfl c) = b
    rw [← HomotopyGroup.map_comp]
    exact hc

/-- The right leg is treated using the actual symmetry homeomorphism, whose
stored path is reversed. No arbitrary basepoint conjugation is suppressed. -/
theorem rightEnd_piOne_bijective_of_equal_kernel
    [PathConnectedSpace A] [PathConnectedSpace B] [PathConnectedSpace C]
    (a : A) (hf : Function.Surjective (HomotopyGroup.piMap 0 f.hom (x := a) rfl))
    (hg : Function.Surjective (HomotopyGroup.piMap 0 g.hom (x := a) rfl))
    (hker : (HomotopyGroup.piMap 0 f.hom (x := a) rfl).ker =
      (HomotopyGroup.piMap 0 g.hom (x := a) rfl).ker) :
    Function.Bijective (HomotopyGroup.piMap 0 (gapRightEndpoint e) (x := g a) rfl) := by
  let := pathConnectedSpace f g sq a
  have hgap := gap_isHomotopyConnectedMap f g sq 1 1 1 (by omega)
    (isHomotopyConnectedMap_one_of_piOne_surjective f.hom a hf)
    (isHomotopyConnectedMap_one_of_piOne_surjective g.hom a hg)
  let := subsingleton_homotopyGroup_zero a
  let := pathConnectedSpace_of_subsingleton_pi_zero (gap f g sq a)
    ((hgap.homotopyGroupMap_zero_surjective a).subsingleton)
  let s := HomotopyPullback.symmetryHomeomorph (gapLeftEndpoint e) (gapRightEndpoint e)
  let := s.pathConnectedSpace
  let k := s.toHomotopyEquiv.toFun.comp (gap f g sq)
  have hk : Function.Surjective (HomotopyGroup.piMap 0 k (x := a) rfl) := by
    intro b
    obtain ⟨c, hc⟩ :=
      (homotopyGroupMap_bijective_of_homotopyEquiv s.toHomotopyEquiv rfl 1).surjective b
    obtain ⟨d, rfl⟩ := hgap.homotopyGroupMap_surjective a 1 (by omega) c
    refine ⟨d, ?_⟩
    change HomotopyGroup.map (N := Fin 1) (s.toHomotopyEquiv.toFun.comp (gap f g sq)) rfl d = b
    rw [HomotopyGroup.map_comp (gap f g sq) rfl s.toHomotopyEquiv.toFun rfl]
    exact hc
  refine ⟨?_, ?_⟩
  · exact HomotopyPullback.piOne_injective_of_gap_surjective
      (gapRightEndpoint e) (gapLeftEndpoint e) k a hk hker.le
  · apply HomotopyPullback.piOne_surjective_of_baseProjection_surjective
      (gapRightEndpoint e) (gapLeftEndpoint e) (k a)
    intro b
    obtain ⟨c, hc⟩ := hf b
    refine ⟨HomotopyGroup.piMap 0 k rfl c, ?_⟩
    change HomotopyGroup.map (N := Fin 1) _ rfl (HomotopyGroup.map _ rfl c) = b
    rw [← HomotopyGroup.map_comp]
    exact hc

/-- Two original plus constructions with the same specified subgroup give
actual Pi-one bijections of both legs of their supplied double cylinder. -/
theorem plus_legs_piOne_bijective
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ N) :
    Function.Bijective (HomotopyGroup.piMap 0 (gapLeftEndpoint e) (x := f a) rfl) ∧
      Function.Bijective (HomotopyGroup.piMap 0 (gapRightEndpoint e) (x := g a) rfl) := by
  let := hf.sourcePathConnected
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  have hsf := (basedPiOneMap_surjective_iff f.hom γ).mp hf.surjective
  have hsg := (basedPiOneMap_surjective_iff g.hom δ).mp hg.surjective
  have hker : (HomotopyGroup.piMap 0 f.hom (x := a) rfl).ker =
      (HomotopyGroup.piMap 0 g.hom (x := a) rfl).ker := by
    rw [← basedPiOneMap_ker f.hom γ, ← basedPiOneMap_ker g.hom δ,
      hf.kernelEq, hg.kernelEq]
  exact ⟨leftEnd_piOne_bijective_of_equal_kernel f g sq a hsf hsg hker,
    rightEnd_piOne_bijective_of_equal_kernel f g sq a hsf hsg hker⟩

end TopCat.DoubleCylinder
