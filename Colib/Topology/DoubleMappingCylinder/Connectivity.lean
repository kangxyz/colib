/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.DoubleMappingCylinder.GapConnectivity
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Vanishing
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.VanishingTransport
public import Colib.Topology.HomotopyPullback.ConnectivityReflection

/-!
# Finite vanishing of the original double mapping cylinder

If all original span spaces have singleton homotopy sets below `n+2`, their actual pushout
double cylinder has the same bound. The genuine finite gap theorem, actual pullback fibers
and the fiber sequence give this closure. The cutoff two is explicit, and actual cylinder
paths establish all component coverage; no separation or attaching-map HEP is assumed.
-/
/-! Implementation provenance: `Quillen/Topology/DoubleMappingCylinder/Connectivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

include f g sq

/-- Original endpoint paths and the full cylinder join every pushout point to one left endpoint.
-/
theorem pathConnectedSpace (a₀ : A) [PathConnectedSpace B] [PathConnectedSpace C] :
    PathConnectedSpace D := by
  have hj (d : D) : Joined (gapLeftEndpoint e (f a₀)) d := by
    rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) d with
      ⟨⟨a, t⟩, hd⟩ | ⟨b | c, hd⟩
    · change l (a, t) = d at hd
      subst d
      let p : Path (gapLeftEndpoint e (f a)) (l (a, t)) := {
        toFun s := l (a, ULift.up (s * t.down))
        continuous_toFun := l.hom.continuous.comp (by fun_prop)
        source' := by
          simp only [zero_mul]
          exact (gap f g sq a).property.1
        target' := by simp only [one_mul]; rfl }
      exact ((PathConnectedSpace.joined (f a₀) (f a)).map
        (gapLeftEndpoint e).continuous).trans ⟨p⟩
    · change gapLeftEndpoint e b = d at hd
      subst d
      exact (PathConnectedSpace.joined (f a₀) b).map (gapLeftEndpoint e).continuous
    · change gapRightEndpoint e c = d at hd
      subst d
      let p : Path (gapLeftEndpoint e (f a₀)) (gapRightEndpoint e (g a₀)) :=
        ⟨(gap f g sq a₀).val.2.2, (gap f g sq a₀).property.1,
          (gap f g sq a₀).property.2⟩
      exact (show Joined _ _ from ⟨p⟩).trans
        ((PathConnectedSpace.joined (g a₀) c).map (gapRightEndpoint e).continuous)
  exact ⟨⟨gapLeftEndpoint e (f a₀)⟩, fun x y ↦ (hj x).symm.trans (hj y)⟩

/-- The original double-cylinder pushout preserves finite vanishing in the displayed range,
including every original point and degree zero. -/
theorem homotopyGroup_subsingleton (a₀ : A) (n : ℕ)
    (hA : ∀ a k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k A a))
    (hB : ∀ b k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k B b))
    (hC : ∀ c k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k C c))
    (d : D) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k D d) := by
  let := pathConnectedSpace_of_subsingleton_pi_zero (f a₀) (hB (f a₀) 0 (by omega))
  let := pathConnectedSpace_of_subsingleton_pi_zero (g a₀) (hC (g a₀) 0 (by omega))
  let := pathConnectedSpace f g sq a₀
  have hf : IsHomotopyConnectedMap f.hom (n + 1) :=
    isHomotopyConnectedMap_of_vanishing f.hom a₀ (n + 1)
      (fun a j hj ↦ hA a j (by omega)) (fun b j hj ↦ hB b j (by omega))
  have hg : IsHomotopyConnectedMap g.hom (n + 1) :=
    isHomotopyConnectedMap_of_vanishing g.hom a₀ (n + 1)
      (fun a j hj ↦ hA a j (by omega)) (fun c j hj ↦ hC c j (by omega))
  have hgap := gap_isHomotopyConnectedMap f g sq (n + 1) (n + 1) (n + 1)
    (by omega) hf hg
  have hp (z : HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e))
      (j : ℕ) (hj : j < n + 2) : Subsingleton (HomotopyGroup.Pi j _ z) :=
    hgap.subsingleton_target j (by omega) (fun a ↦ hA a j hj) z
  have hproj := isHomotopyConnectedMap_of_vanishing
    (HomotopyPullback.baseProjection (gapLeftEndpoint e) (gapRightEndpoint e))
    (gap f g sq a₀) (n + 1)
    (fun z j hj ↦ hp z j (by omega)) (fun c j hj ↦ hC c j (by omega))
  have hleft := HomotopyPullback.isHomotopyConnectedMap_of_baseProjection
    (gapLeftEndpoint e) (gapRightEndpoint e) (g a₀) (n + 1) hproj
  exact hleft.subsingleton_target k (by omega) (fun b ↦ hB b k hk) d

end TopCat.DoubleCylinder

attribute [colib_ref "quillen" "Quillen/Topology/DoubleMappingCylinder/Connectivity.lean:35"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  TopCat.DoubleCylinder.pathConnectedSpace

attribute [colib_ref "quillen" "Quillen/Topology/DoubleMappingCylinder/Connectivity.lean:65"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  TopCat.DoubleCylinder.homotopyGroup_subsingleton
