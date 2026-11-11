module
import Colib.KTheory.Bass.ModelDiagramStableEquivalence

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology Topology.LoopPrespectrum KTheory.Bass
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F G : C ⥤ WideSubcategory preservesZero.{w})

example (η : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor)
    (hη : ∀ X, IsStableEquivalence (η.app X)) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map η).app X) :=
  modelDiagramIterate_map_isStableEquivalence Q i F G η hη X

example (η : F ⟶ G) (e : ∀ X, (F.obj X).obj.Obj ≌ (G.obj X).obj.Obj)
    (he : ∀ X, (e X).functor = (η.app X).hom.toFunctor)
    (hinv : ∀ X, IsExact (G.obj X).obj.waldhausen.cof (G.obj X).obj.waldhausen.weq
      (F.obj X).obj.waldhausen.cof (F.obj X).obj.waldhausen.weq (e X).inverse)
    (X : C) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (((strictDiagramIterate Q i).map (Functor.whiskerRight η prespectrumFunctor)).app X)) :=
  modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence Q i F G η e he hinv X _
