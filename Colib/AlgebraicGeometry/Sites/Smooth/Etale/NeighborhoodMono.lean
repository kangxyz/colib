/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodPullbackNaturality

/-! # Injective coefficient maps on actual étale neighborhood values -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (X : SmoothSite S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left)

/-- An objectwise injective coefficient map remains injective on the original
marked neighborhood value. The proof uses actual common refinements. -/
theorem etaleNeighborhoodValue_map_injective
    {F G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (a : F ⟶ G)
    (ha : ∀ V, Function.Injective (a.app V)) :
    Function.Injective ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map a) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨A, x, rfl⟩ := exists_etaleNeighborhood_representative X ξ F z
  have hx : toEtaleNeighborhoodValue X ξ A G (a.app _ x) = 0 := by
    have hn := congrArg (fun f => f x) (toEtaleNeighborhoodValue_naturality X ξ a A)
    exact hn.symm.trans hz
  obtain ⟨B, f, hf⟩ := (toEtaleNeighborhoodValue_eq_zero_iff X ξ G A _).mp hx
  apply (toEtaleNeighborhoodValue_eq_zero_iff X ξ F A x).mpr
  refine ⟨B, f, ?_⟩
  apply ha (op ((etaleNeighborhoodToSmooth X ξ).obj B))
  rw [map_zero]
  have hn := congrArg (fun g => g x)
    (a.naturality ((etaleNeighborhoodToSmooth X ξ).map f).op)
  exact hn.trans hf

end AlgebraicGeometry.Scheme.SmoothSite
