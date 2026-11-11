module
import Colib.KTheory.Waldhausen.Iterated.DiagramNullIdentityAction

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
noncomputable section
example {V W T : WideSubcategory preservesZero.{u}} (f : V ⟶ W) (g : W ⟶ T)
    (η : (CategoryTheory.Waldhausen.IteratedS.zeroHom V T).hom.toFunctor ⟶
      (f ≫ g).hom.toFunctor) (hη : ∀ S, T.obj.waldhausen.weq (η.app S)) :
    ZeroNullUnitCompatible f g (prespectrumCompositeZeroNullHomotopy f g η hη) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible f g η hη
example {I : Type u} [Category.{v} I]
    {C F G : I ⥤ WideSubcategory preservesZero.{w}} {r : C ⟶ F} {q : F ⟶ G}
    (H : DiagramNullHomotopy (Functor.whiskerRight r prespectrumFunctor)
      (Functor.whiskerRight q prespectrumFunctor)) {a b : I} (f : a ⟶ b) :
    CoefficientIdentityActionCompatible H f := modelDiagramNull_coefficientCompatible H f
