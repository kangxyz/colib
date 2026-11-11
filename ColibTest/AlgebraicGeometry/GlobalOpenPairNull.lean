module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenPairNull

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry Topology Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped unitInterval
universe u
noncomputable section

example (A : Scheme.OpenPairs.{u})
    (S : (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom).FullSubcategory) :
    (((boundedAboveFlatGlobalSectionEvaluation (op A.left)).obj
      ((pairRestriction.app (op A)).hom.toFunctor.obj S.obj)).obj).Acyclic :=
  pairRestriction_acyclic A S

example (A : Scheme.OpenPairs.{u}ᵒᵖ) (S : (pairSupported.obj A).obj.Obj) :
    (pairOpen.obj A).obj.waldhausen.weq ((pairZeroToOpen A).app S) :=
  pairZeroToOpen_weak A S

example (A : Scheme.OpenPairs.{u}ᵒᵖ) (n : ℕ) (s : unitInterval)
    (x : (prespectrum (pairSupported.obj A)).space n) :
    (pairSupportedOpenNull.homotopy A).level n (s, x) =
      (prespectrumTransformationHomotopy (pairZeroToOpen A)
        (pairZeroToOpen_weak A)).level n (unitInterval.symm s, x) :=
  prespectrumCompositeZeroNullHomotopy_level _ _ _ _ n s x

example {A B : Scheme.OpenPairs.{u}ᵒᵖ} (g : A ⟶ B) (n : ℕ) (s : unitInterval)
    (x : (prespectrum (pairSupported.obj A)).space n) :
    (prespectrumMap (pairOpen.map g)).map n ((pairSupportedOpenNull.homotopy A).level n (s, x)) =
      (pairSupportedOpenNull.homotopy B).level n
        (s, (prespectrumMap (pairSupported.map g)).map n x) :=
  pairSupportedOpenNull.naturality g n s x

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (S : ((ParameterModels.supported f).obj X).obj.Obj) :
    ((ParameterModels.openModel f).obj X).obj.waldhausen.weq
      ((ParameterModels.zeroToOpen f X).app S) := ParameterModels.zeroToOpen_weak f X S

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f).obj X)).space n) :
    ((ParameterModels.supportedOpenNull f).homotopy X).level n (s, x) =
      (prespectrumTransformationHomotopy (ParameterModels.zeroToOpen f X)
        (ParameterModels.zeroToOpen_weak f X)).level n (unitInterval.symm s, x) :=
  prespectrumCompositeZeroNullHomotopy_level _ _ _ _ n s x
