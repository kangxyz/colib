/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.SmallModelTransformations
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# The actual native unit triangle contracts to the reflexive track

An actual pair of weak transformations whose composite is the specified source
equality transport gives a relative contraction after that source transport. The
proof uses the original composition triangle and the identity cylinder, including
its degree-zero based-loop proof. No zero endotransformation is assumed weak.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum
universe u

namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} {F G E : V ⟶ W}
  (e : F = E) (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
  (θ : G.hom.toFunctor ⟶ E.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
  (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

/-- The two original transformation tracks, with only their source endpoint transported. -/
def prespectrumTransformationUnitHomotopy :
    Homotopy (prespectrumMap E) (prespectrumMap E) :=
  ((prespectrumTransformationHomotopy η hη).trans
    (prespectrumTransformationHomotopy θ hθ)).cast (congrArg prespectrumMap e) rfl

/-- The actual unit triangle contracts relatively when its composite is source transport. -/
def prespectrumTransformationUnitRelHomotopy
    (hcomp : η ≫ θ = modelEqToHom e) :
    (prespectrumTransformationUnitHomotopy e η θ hη hθ).RelHomotopy
      (Homotopy.refl (prespectrumMap E)) := by
  cases e
  have he : prespectrumTransformationHomotopy (η ≫ θ)
      (fun A => W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) =
        Homotopy.refl (prespectrumMap F) := by
    simpa only [hcomp, modelEqToHom_eq, eqToHom_refl] using
      (prespectrumTransformationHomotopy_identity F
        (fun A => W.obj.waldhausen.weq.id_mem (F.hom.toFunctor.obj A)))
  refine (prespectrumTransformationCompositionHomotopy η θ hη hθ).symm.ofLevels
    (prespectrumTransformationUnitHomotopy rfl η θ hη hθ)
    (Homotopy.refl (prespectrumMap F)) (fun _ => rfl) ?_
  intro n
  exact (congrArg (fun K => K.level n) he).symm

/-- Native right-unit whiskering retains the complete precomposed transformation track. -/
theorem prespectrumModelWhiskerLeftIdHomotopy_level
    (E : V ⟶ W) {P : W ⟶ W}
    (δ : P.hom.toFunctor ⟶ (𝟙 W : W ⟶ W).hom.toFunctor)
    (hδ : ∀ A, W.obj.waldhausen.weq (δ.app A)) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := E ≫ P) (G := E)
      (modelWhiskerLeftId E δ) (fun A => hδ (E.hom.toFunctor.obj A))).level n =
        (Homotopy.precomp (prespectrumMap E)
          (prespectrumTransformationHomotopy δ hδ)).level n := by
  simpa only [modelWhiskerLeftId_eq] using
    (prespectrumTransformationHomotopy_precomp_level δ hδ E n)

end CategoryTheory.Waldhausen.IteratedS
