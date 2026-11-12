module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberLocalizationModels

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules Opposite Topology
open Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.weq
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.weq
      (boundedAboveFlatCoefficientSupportedFiberForget f T a) :=
  boundedAboveFlatCoefficientSupportedFiberForget_exact f T a

example {a b : Under R} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T).map g ≫
        (boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T).app b =
      (boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T).map g :=
  (boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T).naturality g

example (a : Under R) (S : BoundedAboveFlatCoefficientSupportedFiberSections f T a) :
    (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientSupportedFiberZeroToOpen f T a).app S) :=
  boundedAboveFlatCoefficientSupportedFiberZeroToOpen_weak f T a S

example (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a).map m
      (ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
          a).map m) (s, x)) =
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level m (s, x) :=
  boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_cylinder f T a m s x

example (a : Under R) :
    BoundedAboveFlatCoefficientSupportedFiberSections f T a ≌
      AcyclicCategory (boundedAboveFlatCoefficientSupportedOpenNested f T a) :=
  boundedAboveFlatCoefficientSupportedFiberAcyclicEquivalence f T a

example (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a) :=
  boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence f T a

example (a : Under R) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      ((boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a)) :=
  boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence f T a _

example {C : Type u} [Category C] {F G : C ⥤ LoopPrespectrum.{u + 1}}
    (α : F ⟶ G) {X Y : C} (g : X ⟶ Y) :
    (mappingConeDiagram α).map g =
      mappingConeMap (Arrow.homMk (F.map g) (G.map g) (α.naturality g)) :=
  mappingConeDiagram_map α g

example {C : Type u} [Category C] {F G K : C ⥤ LoopPrespectrum.{u + 1}}
    (α : F ⟶ G) (β : G ⟶ K)
    (H : ∀ X, Homotopy (α.app X ≫ β.app X) (zeroHom (F.obj X) (K.obj X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (K.map g).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x)) (X : C) :
    (mappingConeDescTransformation α β H hH).app X =
      mappingConeDesc (α.app X) (β.app X) (H X) := rfl
