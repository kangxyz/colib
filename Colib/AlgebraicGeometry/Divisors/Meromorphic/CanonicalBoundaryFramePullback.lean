/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceBoundaryCore
public import Colib.AlgebraicGeometry.Modules.FrameSectionUniqueness
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryOpenSectionPullback

/-! # Naturality of the original Cartier difference boundary frame

Both sides are the specified native isomorphisms. Equality is proved by evaluating
on a single actual section over the whole boundary, not by choosing a new frame.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf
namespace Stacks.Divisors

/-- Support avoidance is preserved by the prescribed commutative square. -/
theorem avoids_support_comap_square {B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    (w : b ≫ i = i' ≫ f) (D : X.IdealSheafData)
    (hD : ∀ y : B, i y ∉ D.support) : ∀ y : B', i' y ∉ (D.comap f).support := by
  intro y
  rw [Scheme.IdealSheafData.support_comap]
  change f (i' y) ∉ D.support
  have hw := congrArg (fun a : B' ⟶ X => a y) w
  change i (b y) = f (i' y) at hw
  rw [← hw]
  exact hD (b y)

/-- The canonical boundary frame of the actual pulled-back Cartier difference is
exactly the square pullback of the original frame, on the full boundary scheme. -/
theorem differenceSheafBoundaryIso_pullback_square {B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    (w : b ≫ i = i' ≫ f) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f D] [IsPullbackDefined f E]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support) :
    (Scheme.Modules.pullback i').mapIso (differenceSheafPullbackIso f D E) ≪≫
      differenceSheafBoundaryIso i' (D.comap f) (E.comap f)
        (avoids_support_comap_square b i i' f w D hD)
        (avoids_support_comap_square b i i' f w E hE) =
    pullbackBoundaryTrivialization b i i' f w (differenceSheaf D E)
      (differenceSheafBoundaryIso i D E hD hE) := by
  let U := canonicalDifferenceRegularOpen E
  let V := f ⁻¹ᵁ U
  let N := differenceSheaf D E
  let N' := differenceSheaf (D.comap f) (E.comap f)
  let ρ := differenceSheafPullbackIso f D E
  let τ := differenceSheafBoundaryIso i D E hD hE
  let hD' := avoids_support_comap_square b i i' f w D hD
  let hE' := avoids_support_comap_square b i i' f w E hE
  let τ' := differenceSheafBoundaryIso i' (D.comap f) (E.comap f) hD' hE'
  let a := canonicalDifferenceTensorSection D E U (idealOneSection E)
  let c := pullbackSectionHom f N U V le_rfl a
  let d := (pullbackIdealSheafComapIso f E inferInstance).hom.val.app (op V)
    (pullbackSectionHom f (negativeTwist' E) U V le_rfl (idealOneSection E))
  have hd : idealSheafSection (E.comap f) d = (1 : Γ(X', V)) :=
    idealSheafSection_pullbackIdealOne_preimage f E U (idealOneSection E)
      (idealSheafSection_idealOneSection E)
  have hc : ρ.hom.app V c = canonicalDifferenceTensorSection (D.comap f) (E.comap f) V d := by
    have H := differenceSheafPullbackIso_tensorSection_preimage f D E U
      ((canonicalSection' D).eval (op U)) (idealOneSection E)
    change ρ.hom.app V c = _ at H
    rw [invertibleSheafPullbackIso_canonicalSection_preimage f D U] at H
    exact H
  have hi : (⊤ : B.Opens) ≤ i ⁻¹ᵁ U :=
    (preimage_canonicalDifferenceRegularOpen_eq_top i E hE).ge
  have hi' : (⊤ : B'.Opens) ≤ i' ⁻¹ᵁ V := by
    intro y _
    change f (i' y) ∈ U
    have hw := congrArg (fun q : B' ⟶ X => q y) w
    change i (b y) = f (i' y) at hw
    rw [← hw]
    exact hi (by trivial)
  have ha : τ.hom.app ⊤ (pullbackSectionHom i N U ⊤ hi a) = (1 : Γ(B, ⊤)) := by
    apply frame_pullbackSectionHom_top_of_preimage i N U τ a hi
    exact differenceSheafBoundaryIso_tensor_canonical_preimage i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE)
      U (idealOneSection E) (idealSheafSection_idealOneSection E)
  have ha' : τ'.hom.app ⊤
      (pullbackSectionHom i' N' V ⊤ hi'
        (canonicalDifferenceTensorSection (D.comap f) (E.comap f) V d)) =
      (1 : Γ(B', ⊤)) := by
    apply frame_pullbackSectionHom_top_of_preimage i' N' V τ' _ hi'
    exact differenceSheafBoundaryIso_tensor_canonical_preimage i' (D.comap f) (E.comap f)
      (comap_eq_top_of_avoids_support i' (D.comap f) hD')
      (comap_eq_top_of_avoids_support i' (E.comap f) hE') V d hd
  let z := pullbackSectionHom i' ((Scheme.Modules.pullback f).obj N) V ⊤ hi' c
  apply Scheme.Modules.frame_eq_of_same_section_one _ _ z
  · change τ'.hom.app ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullback i').map ρ.hom) ⊤ z) = _
    have hn := Scheme.Modules.pullbackSection_naturality i' ρ.hom V ⊤ hi' c
    change Scheme.Modules.Hom.app ((Scheme.Modules.pullback i').map ρ.hom) ⊤ z =
      pullbackSectionHom i' N' V ⊤ hi' (ρ.hom.app V c) at hn
    rw [hn, hc]
    exact ha'
  · exact Scheme.Modules.pullbackBoundaryTrivialization_openSection_one
      b i i' f w N τ U V hi le_rfl hi' a ha

end Stacks.Divisors
