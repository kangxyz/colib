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

private theorem boundary_frame_tensor_preimage_of_iso {B X : Scheme.{u}}
    (i : B ⟶ X) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (e : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf)
    (he : e = differenceSheafBoundaryIsoOfComapEqTop i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE))
    (U : X.Opens) (a : Γ(negativeTwist' E, U))
    (ha : idealSheafSection E a = (1 : Γ(X, U))) :
    e.hom.app (i ⁻¹ᵁ U)
      (pullbackSectionHom i (differenceSheaf D E) U (i ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a)) =
      (1 : Γ(B, i ⁻¹ᵁ U)) := by
  exact (congrArg (fun t : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
    SheafOfModules.unit B.ringCatSheaf => t.hom.app (i ⁻¹ᵁ U)
      (pullbackSectionHom i (differenceSheaf D E) U (i ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a))) he).trans
    (differenceSheafBoundaryIso_tensor_canonical_preimage i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE)
      U a ha)

private theorem boundary_frame_tensor_one_of_iso {B X : Scheme.{u}}
    (i : B ⟶ X) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (e : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf)
    (he : e = differenceSheafBoundaryIsoOfComapEqTop i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE))
    (U : X.Opens) (hi : ⊤ ≤ i ⁻¹ᵁ U) (a : Γ(negativeTwist' E, U))
    (ha : idealSheafSection E a = (1 : Γ(X, U))) :
    e.hom.app ⊤ (pullbackSectionHom i (differenceSheaf D E) U ⊤ hi
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a)) =
      (1 : Γ(B, ⊤)) :=
  frame_pullbackSectionHom_top_of_preimage i (differenceSheaf D E) U e
    (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a) hi
    (boundary_frame_tensor_preimage_of_iso i D E hD hE e he U a ha)

private theorem boundary_frame_tensor_one {B X : Scheme.{u}}
    (i : B ⟶ X) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (U : X.Opens) (hi : ⊤ ≤ i ⁻¹ᵁ U) (a : Γ(negativeTwist' E, U))
    (ha : idealSheafSection E a = (1 : Γ(X, U))) :
    (differenceSheafBoundaryIso i D E hD hE).hom.app ⊤
      (pullbackSectionHom i (differenceSheaf D E) U ⊤ hi
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a)) =
      (1 : Γ(B, ⊤)) :=
  boundary_frame_tensor_one_of_iso i D E hD hE (differenceSheafBoundaryIso i D E hD hE)
    (differenceSheafBoundaryIso_eq_ofComap i D E hD hE) U hi a ha

private theorem canonical_tensor_pullback {X' X : Scheme.{u}}
    (f : X' ⟶ X) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f D] [IsPullbackDefined f E]
    (U : X.Opens) (a : Γ(negativeTwist' E, U)) :
    (differenceSheafPullbackIso f D E).hom.app (f ⁻¹ᵁ U)
      (pullbackSectionHom f (differenceSheaf D E) U (f ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a)) =
      Stacks.SheafOfModules.tensorSectionsAt X'.sheaf.obj X'.ringCatSheaf.property
        (op (f ⁻¹ᵁ U)) (divisorSheaf (D.comap f)) (negativeTwist' (E.comap f))
        ((canonicalSection' (D.comap f)).eval (op (f ⁻¹ᵁ U)))
        ((pullbackIdealSheafComapIso f E inferInstance).hom.val.app (op (f ⁻¹ᵁ U))
          (pullbackSectionHom f (negativeTwist' E) U (f ⁻¹ᵁ U) le_rfl a)) := by
  have H := differenceSheafPullbackIso_tensorSection_preimage f D E U
    ((canonicalSection' D).eval (op U)) a
  rw [invertibleSheafPullbackIso_canonicalSection_preimage f D U] at H
  exact H

private theorem frame_mapIso_section_one {B X : Scheme.{u}}
    (i : B ⟶ X) (M N : X.Modules) (e : M ≅ N)
    (τ : (Scheme.Modules.pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (U : X.Opens) (hi : ⊤ ≤ i ⁻¹ᵁ U) (a : Γ(M, U))
    (ha : τ.hom.app ⊤ (pullbackSectionHom i N U ⊤ hi (e.hom.app U a)) =
      (1 : Γ(B, ⊤))) :
    ((Scheme.Modules.pullback i).mapIso e ≪≫ τ).hom.app ⊤
      (pullbackSectionHom i M U ⊤ hi a) = (1 : Γ(B, ⊤)) := by
  exact (congrArg (τ.hom.app ⊤)
    (Scheme.Modules.pullbackSection_naturality i e.hom U ⊤ hi a)).trans ha

private theorem boundary_frame_pullback_tensor_one {B' X' X : Scheme.{u}}
    (i' : B' ⟶ X') (f : X' ⟶ X) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f D] [IsPullbackDefined f E]
    (hD : ∀ y : B', i' y ∉ (D.comap f).support)
    (hE : ∀ y : B', i' y ∉ (E.comap f).support)
    (U : X.Opens) (hi : ⊤ ≤ i' ⁻¹ᵁ (f ⁻¹ᵁ U)) (a : Γ(negativeTwist' E, U))
    (ha : idealSheafSection E a = (1 : Γ(X, U))) :
    ((Scheme.Modules.pullback i').mapIso (differenceSheafPullbackIso f D E) ≪≫
      differenceSheafBoundaryIso i' (D.comap f) (E.comap f) hD hE).hom.app ⊤
      (pullbackSectionHom i' ((Scheme.Modules.pullback f).obj (differenceSheaf D E))
        (f ⁻¹ᵁ U) ⊤ hi (pullbackSectionHom f (differenceSheaf D E) U (f ⁻¹ᵁ U)
          le_rfl (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a))) =
      (1 : Γ(B', ⊤)) := by
  let d := (pullbackIdealSheafComapIso f E inferInstance).hom.val.app (op (f ⁻¹ᵁ U))
    (pullbackSectionHom f (negativeTwist' E) U (f ⁻¹ᵁ U) le_rfl a)
  have hd : idealSheafSection (E.comap f) d = (1 : Γ(X', f ⁻¹ᵁ U)) :=
    idealSheafSection_pullbackIdealOne_preimage f E U a ha
  let ρ := differenceSheafPullbackIso f D E
  let c := pullbackSectionHom f (differenceSheaf D E) U (f ⁻¹ᵁ U) le_rfl
    (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a)
  apply frame_mapIso_section_one i' _ _ ρ
    (differenceSheafBoundaryIso i' (D.comap f) (E.comap f) hD hE) (f ⁻¹ᵁ U) hi c
  have hc := canonical_tensor_pullback f D E U a
  change ρ.hom.app (f ⁻¹ᵁ U) c =
    Stacks.SheafOfModules.tensorSectionsAt X'.sheaf.obj X'.ringCatSheaf.property
      (op (f ⁻¹ᵁ U)) (divisorSheaf (D.comap f)) (negativeTwist' (E.comap f))
      ((canonicalSection' (D.comap f)).eval (op (f ⁻¹ᵁ U))) d at hc
  exact (congrArg (fun t =>
    (differenceSheafBoundaryIso i' (D.comap f) (E.comap f) hD hE).hom.app ⊤
      (pullbackSectionHom i' (differenceSheaf (D.comap f) (E.comap f))
        (f ⁻¹ᵁ U) ⊤ hi t)) hc).trans
    (boundary_frame_tensor_one i' (D.comap f) (E.comap f) hD hE (f ⁻¹ᵁ U) hi d hd)

/-- Transport a frame evaluation without reducing either frame's definition. -/
private theorem frame_value_transport {Z : Scheme.{u}} {M : Z.Modules}
    (e e₀ : M ≅ SheafOfModules.unit Z.ringCatSheaf) (he : e = e₀)
    (s s₀ : Γ(M, ⊤)) (hs : s = s₀)
    (h : e₀.hom.app ⊤ s₀ = (1 : Γ(Z, ⊤))) :
    e.hom.app ⊤ s = (1 : Γ(Z, ⊤)) := by
  exact (congrArg (fun t => t.hom.app ⊤ s) he).trans
    ((congrArg (e₀.hom.app ⊤) hs).trans h)

/-- Keep both large native frames and the selected section opaque while applying
frame uniqueness. The equalities identify actual constructions, not assumed
naturality: both scalar evaluations are derived below from the tensor lemmas. -/
private theorem boundary_square_frame_eq_of_iso {B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    (w : b ≫ i = i' ≫ f) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f D] [IsPullbackDefined f E]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (U : X.Opens) (hi : ⊤ ≤ i ⁻¹ᵁ U) (hi' : ⊤ ≤ i' ⁻¹ᵁ (f ⁻¹ᵁ U))
    (a : Γ(negativeTwist' E, U)) (ha : idealSheafSection E a = (1 : Γ(X, U)))
    (eL eR : (Scheme.Modules.pullback i').obj
      ((Scheme.Modules.pullback f).obj (differenceSheaf D E)) ≅
      SheafOfModules.unit B'.ringCatSheaf)
    (heL : eL = (Scheme.Modules.pullback i').mapIso (differenceSheafPullbackIso f D E) ≪≫
      differenceSheafBoundaryIso i' (D.comap f) (E.comap f)
        (avoids_support_comap_square b i i' f w D hD)
        (avoids_support_comap_square b i i' f w E hE))
    (heR : eR = pullbackBoundaryTrivialization b i i' f w (differenceSheaf D E)
      (differenceSheafBoundaryIso i D E hD hE))
    (z : Γ((Scheme.Modules.pullback i').obj
      ((Scheme.Modules.pullback f).obj (differenceSheaf D E)), ⊤))
    (hz : z = pullbackSectionHom i' ((Scheme.Modules.pullback f).obj (differenceSheaf D E))
      (f ⁻¹ᵁ U) ⊤ hi' (pullbackSectionHom f (differenceSheaf D E) U (f ⁻¹ᵁ U)
        le_rfl (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
          (op U) (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a))) :
    eL = eR := by
  have hL : eL.hom.app ⊤ z = (1 : Γ(B', ⊤)) :=
    frame_value_transport eL _ heL z _ hz
      (boundary_frame_pullback_tensor_one i' f D E
        (avoids_support_comap_square b i i' f w D hD)
        (avoids_support_comap_square b i i' f w E hE) U hi' a ha)
  have hR : eR.hom.app ⊤ z = (1 : Γ(B', ⊤)) :=
    frame_value_transport eR _ heR z _ hz
      (Scheme.Modules.pullbackBoundaryTrivialization_openSection_one b i i' f w
        (differenceSheaf D E) (differenceSheafBoundaryIso i D E hD hE)
        U (f ⁻¹ᵁ U) hi le_rfl hi'
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
          (op U) (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) a)
        (boundary_frame_tensor_one i D E hD hE U hi a ha))
  exact Scheme.Modules.frame_eq_of_same_section_one eL eR z hL hR

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
  let a := Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
            (op U)
    (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) (idealOneSection E)
  have hi : (⊤ : B.Opens) ≤ i ⁻¹ᵁ U :=
    (preimage_canonicalDifferenceRegularOpen_eq_top i E hE).ge
  have hi' : (⊤ : B'.Opens) ≤ i' ⁻¹ᵁ V := by
    intro y _
    change f (i' y) ∈ U
    have hw := congrArg (fun q : B' ⟶ X => q y) w
    change i (b y) = f (i' y) at hw
    rw [← hw]
    exact hi (by trivial)
  let z := pullbackSectionHom i' ((Scheme.Modules.pullback f).obj N) V ⊤ hi'
    (pullbackSectionHom f N U V le_rfl a)
  exact boundary_square_frame_eq_of_iso b i i' f w D E hD hE U hi hi'
    (idealOneSection E) (idealSheafSection_idealOneSection E) _ _ rfl rfl z rfl

end Stacks.Divisors
