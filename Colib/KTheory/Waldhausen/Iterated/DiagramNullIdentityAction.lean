/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNullUnit

/-!
# Identity actions along the original coefficient maps of a diagram null

A whole coefficient-natural Model-diagram null transports identity-action interchange
at the target coefficient object to interchange with the two original coefficient tracks.
Both interval parameters and every prespectrum level are retained. The generic theorem
requires the actual target identity-action interchange and derives the coefficient step
from the naturality of the same supplied diagram null.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology

/-- Two whole homotopies commute with the indicated tracks at both independent times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/DiagramNullIdentityAction.lean:26"
  "adaptation" "Original whole reversed-null identity and independent coefficient-action times."]
def TrackInterchange {E₀ E₁ F₀ F₁ : LoopPrespectrum.{w}}
    {f₀ g₀ : E₀ ⟶ F₀} {f₁ g₁ : E₁ ⟶ F₁}
    (N₀ : Homotopy f₀ g₀) (N₁ : Homotopy f₁ g₁)
    {u₀ u₁ : E₀ ⟶ E₁} {v₀ v₁ : F₀ ⟶ F₁}
    (A : Homotopy u₀ u₁) (B : Homotopy v₀ v₁) : Prop :=
  ∀ (n : ℕ) (s t : unitInterval) (x : E₀.space n),
    N₁.level n (s, A.level n (t, x)) = B.level n (t, N₀.level n (s, x))

/-- Identity-action interchange lifts along one original coefficient arrow of the same null. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/DiagramNullIdentityAction.lean:35"
  "adaptation" "Original whole reversed-null identity and independent coefficient-action times."]
def CoefficientIdentityActionCompatible {I : Type u} [Category.{v} I]
    {C F G : I ⥤ WideSubcategory preservesZero.{w}} {r : C ⟶ F} {q : F ⟶ G}
    (H : DiagramNullHomotopy
      (Functor.whiskerRight r prespectrumFunctor) (Functor.whiskerRight q prespectrumFunctor))
    {a b : I} (f : a ⟶ b) : Prop :=
  ∀ (α : 𝟭 (C.obj b).obj.Obj ≅ 𝟭 (C.obj b).obj.Obj)
    (β : 𝟭 (G.obj b).obj.Obj ≅ 𝟭 (G.obj b).obj.Obj),
    IdentityActionInterchange (H.homotopy b) α β →
      TrackInterchange (H.homotopy a) (H.homotopy b)
        (prespectrumIsoHomotopy (C.map f)
          (CategoryTheory.Functor.IdentityAutomorphism.onFunctor (C.map f).hom.toFunctor α))
        (prespectrumIsoHomotopy (G.map f)
          (CategoryTheory.Functor.IdentityAutomorphism.onFunctor (G.map f).hom.toFunctor β))

/-- The original coefficient equation lifts interchange without changing the null or its times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/DiagramNullIdentityAction.lean:49"
  "adaptation" "Original whole reversed-null identity and independent coefficient-action times."]
theorem modelDiagramNull_coefficientCompatible {I : Type u} [Category.{v} I]
    {C F G : I ⥤ WideSubcategory preservesZero.{w}} {r : C ⟶ F} {q : F ⟶ G}
    (H : DiagramNullHomotopy
      (Functor.whiskerRight r prespectrumFunctor) (Functor.whiskerRight q prespectrumFunctor))
    {a b : I} (f : a ⟶ b) : CoefficientIdentityActionCompatible H f := by
  intro α β hU n s t x
  have hC := prespectrumIsoHomotopy_onFunctor_apply (C.map f) α n t x
  have hG := prespectrumIsoHomotopy_onFunctor_apply (G.map f) β n t
    ((H.homotopy a).level n (s, x))
  have hN := H.naturality f n s x
  have h := hU n s t ((prespectrumMap (C.map f)).map n x)
  exact (congrArg (fun y => (H.homotopy b).level n (s, y)) hC).trans
    (h.trans ((congrArg (fun y => (prespectrumIsoHomotopy (𝟙 (G.obj b)) β).level n
      (t, y)) hN.symm).trans hG.symm))

end CategoryTheory.Waldhausen.IteratedS
