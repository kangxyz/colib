module
import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open KTheory.Bass
universe u v w
noncomputable section

example {S T : Arrow (Arrow LoopPrespectrum.{w})} (a : S ⟶ T) :
    mappingConeInclusion (strictSquareLoopedConeFunctor.map a) ≫
        StrictSquare.loopedConeCofiberComparison a =
      strictSquareLoopedConeFunctor.map (StrictSquare.coneSquareInclusion a) :=
  StrictSquare.loopedConeCofiberComparison_inclusion a

example {S T : Arrow (Arrow LoopPrespectrum.{w})} (a : S ⟶ T)
    (n : ℕ) (r t : unitInterval)
    (γ : Path ((mappingCone (StrictSquare.comparison S)).point n)
      ((mappingCone (StrictSquare.comparison S)).point n)) :
    Path.toContinuousMap ((StrictSquare.loopedConeCofiberComparison a).map n
      (ReducedMappingCone.cylinder ((strictSquareLoopedConeFunctor.obj S).point n)
        ((strictSquareLoopedConeFunctor.obj T).point n)
        ((strictSquareLoopedConeFunctor.map a).map n) (r, γ))) t =
      (StrictSquare.coneInterchangeIso a).hom.map n
        (ReducedMappingCone.cylinder ((mappingCone (StrictSquare.comparison S)).point n)
          ((mappingCone (StrictSquare.comparison T)).point n)
          ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n) (r, γ t)) :=
  StrictSquare.loopedConeCofiberComparison_cylinder a n r t γ

example {S T S' T' : Arrow (Arrow LoopPrespectrum.{w})} {a : S ⟶ T} {b : S' ⟶ T'}
    (k : Arrow.mk a ⟶ Arrow.mk b) :
    mappingConeMap (strictSquareLoopedConeFunctor.mapArrow.map k) ≫
        StrictSquare.loopedConeCofiberComparison b =
      StrictSquare.loopedConeCofiberComparison a ≫
        strictSquareLoopedConeFunctor.map (StrictSquare.coneSquareMap k) :=
  StrictSquare.loopedConeCofiberComparison_naturality a k

variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F G K : C ⥤ WideSubcategory preservesZero.{w})
  (a : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor)
  (b : G ⋙ prespectrumFunctor ⟶ K ⋙ prespectrumFunctor) (H : DiagramNullHomotopy a b)

example (n : ℕ) (X : C) :
    IsStableEquivalence
      (mappingConeFiberComparison (((strictDiagramIterate Q n).map a).app X)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence Q F G a n X

example
    (hdesc : ∀ X, IsStableEquivalence
      (mappingConeDesc (a.app X) (b.app X) (H.homotopy X))) (n : ℕ) (X : C) :
    IsStableEquivalence (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
      (((strictDiagramIterate Q n).map b).app X)
      ((strictDiagramIterateNull Q H n).homotopy X)) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence Q F G K a b H hdesc n X

example
    (hdesc : ∀ X, IsStableEquivalence
      (mappingConeDesc (a.app X) (b.app X) (H.homotopy X))) (n : ℕ) (X : C) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
        (((strictDiagramIterate Q n).map b).app X)
        ((strictDiagramIterateNull Q H n).homotopy X))) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence Q F G K a b H hdesc n X _

example (n : ℕ) (X : C) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
          (((strictDiagramIterate Q n).map b).app X)
          ((strictDiagramIterateNull Q H n).homotopy X)) ≫
      stableFiberConnecting (((strictDiagramIterate Q n).map b).app X) d =
    stableMappingConeConnecting (((strictDiagramIterate Q n).map a).app X)
      (modelDiagramIterateArrow_coneFiber_isStableEquivalence Q F G a n X) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          (((strictDiagramIterate Q n).map b).app X) (((strictDiagramIterate Q n).map a).app X)
          ((strictDiagramIterateNull Q H n).homotopy X)) :=
  modelDiagramIterateCofiberDesc_connecting Q F G K a b H n X d
