/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition

/-!
# Relative pasting for the actual direct-small prespectrum tracks

Equal composite transformations give relatively homotopic concatenated tracks by the
actual two composition triangles. No extra AsSmall lift or normalization is performed.
-/
@[expose] public noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {V W : WideSubcategory preservesZero.{u}} {F G G' H : V ⟶ W}

/-- Paste the two genuine triangles along their equal composite-transformation track. -/
def prespectrumTransformationPastingHomotopy
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (η' : F.hom.toFunctor ⟶ G'.hom.toFunctor) (θ' : G'.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.obj.waldhausen.weq (θ'.app A))
    (hcomp : η ≫ θ = η' ≫ θ') :
    ((prespectrumTransformationHomotopy η hη).trans
      (prespectrumTransformationHomotopy θ hθ)).RelHomotopy
      ((prespectrumTransformationHomotopy η' hη').trans
        (prespectrumTransformationHomotopy θ' hθ')) := by
  have he : prespectrumTransformationHomotopy (η ≫ θ)
      (fun A => W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) =
    prespectrumTransformationHomotopy (η' ≫ θ')
      (fun A => W.obj.waldhausen.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
    congr 1
  have J := prespectrumTransformationCompositionHomotopy η' θ' hη' hθ'
  rw [← he] at J
  exact (prespectrumTransformationCompositionHomotopy η θ hη hθ).symm.trans J

/-- Transporting strict model endpoints changes no point of the actual transformation track. -/
lemma prespectrumTransformationHomotopy_congr_level
    {F G F' G' : V ⟶ W} (eF : F = F') (eG : G = G')
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (η' : F'.hom.toFunctor ⟶ G'.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (h : η ≫ eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) eG) =
      eqToHom (congrArg (fun f : V ⟶ W => f.hom.toFunctor) eF) ≫ η') (n : ℕ) :
    (prespectrumTransformationHomotopy η hη).level n =
      (prespectrumTransformationHomotopy η' hη').level n := by
  cases eF
  cases eG
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
  subst η'
  rfl

end CategoryTheory.Waldhausen.IteratedS
