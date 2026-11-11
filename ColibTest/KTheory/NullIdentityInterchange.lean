module
import Colib.KTheory.Waldhausen.Iterated.TransformationInterchange
import Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityAction

open CategoryTheory Topology
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
noncomputable section
variable {V W : WideSubcategory preservesZero.{u}}
example (F : V ⟶ W)
    (e : 𝟭 W.obj.Obj ≅ 𝟭 W.obj.Obj) (n : ℕ) :
    (prespectrumIsoHomotopy F
      (CategoryTheory.Functor.IdentityAutomorphism.onFunctor F.hom.toFunctor e)).level n =
      ((prespectrumIsoHomotopy (𝟙 W) e).precomp (prespectrumMap F)).level n :=
  prespectrumIsoHomotopy_onFunctor_level F e n
example (F : V ⟶ W)
    (e : 𝟭 W.obj.Obj ≅ 𝟭 W.obj.Obj) (n : ℕ) (t : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumIsoHomotopy F
      (CategoryTheory.Functor.IdentityAutomorphism.onFunctor F.hom.toFunctor e)).level n (t, x) =
      (prespectrumIsoHomotopy (𝟙 W) e).level n (t, (prespectrumMap F).map n x) :=
  prespectrumIsoHomotopy_onFunctor_apply F e n t x
example {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (α : (𝟙 V : V ⟶ V).hom.toFunctor ⟶ (𝟙 V : V ⟶ V).hom.toFunctor)
    (β : (𝟙 W : W ⟶ W).hom.toFunctor ⟶ (𝟙 W : W ⟶ W).hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hα : ∀ X, V.obj.waldhausen.weq (α.app X))
    (hβ : ∀ X, W.obj.waldhausen.weq (β.app X))
    (hF : ∀ X, F.hom.toFunctor.map (α.app X) = β.app (F.hom.toFunctor.obj X))
    (hG : ∀ X, G.hom.toFunctor.map (α.app X) = β.app (G.hom.toFunctor.obj X))
    (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationHomotopy η hη).symm.level n
        (s, (prespectrumTransformationHomotopy α hα).level n (t, x)) =
      (prespectrumTransformationHomotopy β hβ).level n
        (t, (prespectrumTransformationHomotopy η hη).symm.level n (s, x)) :=
  prespectrumTransformationHomotopy_symm_identityAction_interchange η α β hη hα hβ hF hG n s t x
