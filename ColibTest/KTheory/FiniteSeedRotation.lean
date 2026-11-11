module
import Colib.KTheory.Bass.FiniteTwistedTail
import Colib.Topology.Prespectrum.FiniteLoopInnerRotation
open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open Topology.LoopPrespectrum.FiniteParameterLooping
open Topology.LoopPrespectrum.FiniteLoopWords
open Topology.LoopPrespectrum.FiniteLoopWordSlide
open FiniteConeStrength IteratedLoopStrength FiniteLoopStrengthWords NormalizedStageMap
open AssociatedStrength
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C]

example (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram i (F ⋙ parameterLoopingFunctor)).obj X).space n)
    (t : Fin (i + 1) → unitInterval) :
    evaluate (i + 1) F X n
        (((eqToHom (loopDiagram_postcomp i F)).app X).map n z) t =
      Path.toContinuousMap (evaluate i (F ⋙ parameterLoopingFunctor) X n z (Fin.init t))
        (t (Fin.last i)) :=
  Topology.LoopPrespectrum.FiniteLoopInnerRotation.postcomp_evaluate i F X n z t

example (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    loopMap i (transposeIso F).inv ≫
        eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor)) ≫
        (cyclicIso i (F ⋙ parameterLoopingFunctor)).hom ≫
        eqToHom (loopDiagram_postcomp (i + 1) F) =
      eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor)) ≫
        eqToHom (loopDiagram_postcomp (i + 1) F) ≫ (cyclicIso (i + 1) F).hom :=
  Topology.LoopPrespectrum.FiniteLoopInnerRotation.cyclicIso_succ_inner i F

example (i : ℕ) {F G : C ⥤ LoopPrespectrum.{w}}
    (b : F ⟶ G ⋙ parameterLoopingFunctor) (p : G ⟶ G) :
    loopMap i (Functor.whiskerRight b parameterLoopingFunctor) ≫
        loopMap i (transposeIso G).inv ≫ loopMap i (loopMap 2 p) ≫
        eqToHom (loopDiagram_postcomp i (G ⋙ parameterLoopingFunctor)) ≫
        (cyclicIso i (G ⋙ parameterLoopingFunctor)).hom ≫
        eqToHom (loopDiagram_postcomp (i + 1) G) =
      eqToHom (loopDiagram_postcomp i F) ≫ loopMap (i + 1) b ≫
        eqToHom (loopDiagram_postcomp (i + 1) G) ≫
        (cyclicIso (i + 1) G).hom ≫ loopMap (i + 2) p :=
  KTheory.Bass.FiniteSeedRotation.loop_rotation_tail i b p

example (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (a : F ⟶ (strictDiagramFunctor Q).obj F)
    (b : ConeTrack.diagram Q F ⟶
      (strictDiagramFunctor Q).obj (ConeTrack.diagram Q F))
    (p : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (h : (strictDiagramFunctor Q).map a ≫ strengthDiagram Q (ConeTrack.diagram Q F) =
      Functor.whiskerRight b parameterLoopingFunctor ≫
        (transposeIso (ConeTrack.diagram Q (ConeTrack.diagram Q F))).inv ≫
        loopMap 2 p) :
    (strictDiagramFunctor Q).map
        (loopInto i a ≫ (cyclicIso i (ConeTrack.diagram Q F)).hom) ≫
        associatedStrength Q (i + 1) (ConeTrack.diagram Q F) =
      associatedStrength Q i F ≫ loopInto (i + 1)
        (A := ConeTrack.diagram Q F)
        (B := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b ≫
        (cyclicIso (i + 1)
          (ConeTrack.diagram Q (ConeTrack.diagram Q F))).hom ≫
        loopMap (i + 2) p :=
  KTheory.Bass.FiniteSeedRotation.finite_seed_rotation Q i F a b p h

example (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (a : F ⟶ (strictDiagramFunctor Q).obj F)
    (b : ConeTrack.diagram Q F ⟶
      (strictDiagramFunctor Q).obj (ConeTrack.diagram Q F))
    (p : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (q : ConeTrack.diagram Q F ⟶ ConeTrack.diagram Q F)
    (h : (strictDiagramFunctor Q).map a ≫ strengthDiagram Q (ConeTrack.diagram Q F) =
      Functor.whiskerRight b parameterLoopingFunctor ≫
        (transposeIso (ConeTrack.diagram Q (ConeTrack.diagram Q F))).inv ≫
        loopMap 2 p) :
    (strictDiagramFunctor Q).map
        (loopInto i a ≫ (cyclicIso i (ConeTrack.diagram Q F)).hom ≫
          loopMap (i + 1) q) ≫
        associatedStrength Q (i + 1) (ConeTrack.diagram Q F) =
      associatedStrength Q i F ≫ loopInto (i + 1)
        (A := ConeTrack.diagram Q F)
        (B := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b ≫
        (cyclicIso (i + 1)
          (ConeTrack.diagram Q (ConeTrack.diagram Q F))).hom ≫
        loopMap (i + 2) (p ≫ ConeTrack.map Q q) :=
  KTheory.Bass.FiniteTwistedRotation.finite_twisted_rotation Q i F a b p q h

example (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (a : F ⟶ (strictDiagramFunctor Q).obj F)
    (b : ConeTrack.diagram Q F ⟶
      (strictDiagramFunctor Q).obj (ConeTrack.diagram Q F))
    (p : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (q : ConeTrack.diagram Q F ⟶ ConeTrack.diagram Q F)
    (r : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (h : (strictDiagramFunctor Q).map a ≫ strengthDiagram Q (ConeTrack.diagram Q F) =
      Functor.whiskerRight b parameterLoopingFunctor ≫
        (transposeIso (ConeTrack.diagram Q (ConeTrack.diagram Q F))).inv ≫
        loopMap 2 p)
    (hword : p ≫ ConeTrack.map Q q = r) :
    (strictDiagramFunctor Q).map
        (loopInto i a ≫ (cyclicIso i (ConeTrack.diagram Q F)).hom ≫
          loopMap (i + 1) q) ≫
        associatedStrength Q (i + 1) (ConeTrack.diagram Q F) =
      associatedStrength Q i F ≫ loopInto (i + 1)
        (A := ConeTrack.diagram Q F)
        (B := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b ≫
        (cyclicIso (i + 1)
          (ConeTrack.diagram Q (ConeTrack.diagram Q F))).hom ≫
        loopMap (i + 2) r :=
  KTheory.Bass.FiniteTwistedTail.finite_twisted_rotation_of_tail Q i F a b p q r h hword
