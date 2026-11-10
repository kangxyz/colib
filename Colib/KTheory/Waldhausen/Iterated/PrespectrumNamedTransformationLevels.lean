/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.SmallModelTransformations

/-!
# Complete levels for proved names of actual native transformations

A proved transformation equality is eliminated with abstract native arrows. The
weak-equivalence arguments remain arbitrary proofs of the same propositions. No
geometric definition, chosen zero or transformation-cylinder formula is unfolded.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum
universe u

namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- A proved equality of transformations identifies their entire levels, independently
of the witnesses that their components are weak equivalences. -/
theorem prespectrumTransformationHomotopy_level_eq_of_eq
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η θ : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (e : η = θ) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := F) (G := G) η hη).level n =
      (prespectrumTransformationHomotopy (F := F) (G := G) θ hθ).level n := by
  subst θ
  rfl

/-- Precomposition is the whole track of any transformation proved to be the native
left whisker. The native endpoints and the supplied weak witnesses stay explicit. -/
theorem prespectrumModelWhiskerLeftHomotopy_level_of_eq
    {U V W : WideSubcategory preservesZero.{u}}
    (E : U ⟶ V) {P Q : V ⟶ W}
    (μ : P.hom.toFunctor ⟶ Q.hom.toFunctor)
    (hμ : ∀ A, W.obj.waldhausen.weq (μ.app A))
    (θ : (E ≫ P).hom.toFunctor ⟶ (E ≫ Q).hom.toFunctor)
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (eθ : θ = modelWhiskerLeft E μ) (n : ℕ) :
    (Homotopy.precomp (prespectrumMap E)
      (prespectrumTransformationHomotopy (F := P) (G := Q) μ hμ)).level n =
        (prespectrumTransformationHomotopy (F := E ≫ P) (G := E ≫ Q) θ hθ).level n := by
  exact (prespectrumTransformationHomotopy_precomp_level
    (F := P) (G := Q) μ hμ E n).symm.trans
      (prespectrumTransformationHomotopy_level_eq_of_eq
        (F := E ≫ P) (G := E ≫ Q)
        (whiskerLeft E.hom.toFunctor μ) θ
        (fun A => hμ (E.hom.toFunctor.obj A)) hθ
        ((modelWhiskerLeft_eq E μ).symm.trans eθ.symm) n)

end CategoryTheory.Waldhausen.IteratedS
