/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialDiagramNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialTransport

/-! Strict whole-null transport along proved equalities of the actual three tracks. -/
/-!
Implementation provenance: adapted from Quillen at
`SchemeTrackSequentialNullTransport.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
variable (M₀ M₁ M₂ : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A₀ B₀ : Track laurent.op coefficient (M₀ ⋙ prespectrumFunctor))
    (A₁ B₁ : Track laurent.op coefficient (M₁ ⋙ prespectrumFunctor))
    (A₂ B₂ : Track laurent.op coefficient (M₂ ⋙ prespectrumFunctor))
    (h₀ : A₀ = B₀) (h₁ : A₁ = B₁) (h₂ : A₂ = B₂)
    (η : M₀ ⋙ prespectrumFunctor ⟶ M₁ ⋙ prespectrumFunctor)
    (θ : M₁ ⋙ prespectrumFunctor ⟶ M₂ ⋙ prespectrumFunctor)
    (hη : Equivariant A₀ A₁ η) (hθ : Equivariant A₁ A₂ θ)
    (hη' : Equivariant B₀ B₁ η) (hθ' : Equivariant B₁ B₂ θ)
    (N : DiagramNullHomotopy η θ)
    (hN : ∀ r, Equivariant A₀ A₂
      (diagramHomotopyAt (η := η ≫ θ)
        (θ := diagramZeroMap (M₀ ⋙ prespectrumFunctor) (M₂ ⋙ prespectrumFunctor))
        N.homotopy N.naturality r))
    (hN' : ∀ r, Equivariant B₀ B₂
      (diagramHomotopyAt (η := η ≫ θ)
        (θ := diagramZeroMap (M₀ ⋙ prespectrumFunctor) (M₂ ⋙ prespectrumFunctor))
        N.homotopy N.naturality r))

include h₁ in
/-- The original current null is preserved at the same time after the entire track equalities. -/
theorem ordinaryInputNull_comparisonOfEq (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (q : ((currentTelescope A₀).obj X).space n) :
    (comparisonOfEq M₂ A₂ B₂ h₂ X).map n
        (((currentInputNull A₀ A₁ A₂ η θ hη hθ N hN).homotopy X).level n (r, q)) =
      (((ordinaryInputNull M₀ M₁ B₀ B₁ η hη' M₂ B₂ θ hθ' N hN').homotopy X).level n
        (r, (comparisonOfEq M₀ A₀ B₀ h₀ X).map n q)) := by
  subst B₀
  subst B₁
  subst B₂
  exact ordinaryInputNull_comparison M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN X n r q

end KTheory.Bass.SchemeTrackSequentialPresentation
