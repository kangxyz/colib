module
import Colib.KTheory.Bass.NormalizedStageAction
import Colib.Topology.Prespectrum.FiniteLoopWords

open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open KTheory.Bass
open KTheory.Bass.FiniteConeTopology KTheory.Bass.IteratedLoopStrength
open KTheory.Bass.NormalizedStageMap
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C]
variable (Q : C ⥤ Arrow (Arrow C)) (F G : C ⥤ LoopPrespectrum.{w})

example : iteratedStrength Q 0 F = 𝟙 ((strictDiagramFunctor Q).obj F) := rfl
example (j : ℕ) : iteratedStrength Q (j + 1) F =
    strengthDiagram Q (loopDiagram j F) ≫
      Functor.whiskerRight (iteratedStrength Q j F) parameterLoopingFunctor := rfl
example (i : ℕ) (X : C) : (normalized Q i F).obj X =
    loops i ((iterate Q i F).obj X) := normalized_obj Q i F X
example : stageMap Q 0 F = 𝟙 F := rfl
example (j : ℕ) : FiniteLoopWords.loopMap j (𝟙 F) = 𝟙 (loopDiagram j F) :=
  FiniteLoopWords.loopMap_id j F
example (j : ℕ) (f : F ⟶ G) : FiniteLoopWords.loopMap j (f ≫ 𝟙 G) =
    FiniteLoopWords.loopMap j f ≫ FiniteLoopWords.loopMap j (𝟙 G) :=
  FiniteLoopWords.loopMap_comp j f (𝟙 G)

example {L : C ⥤ C} {c : 𝟭 C ⟶ L} (A : KTheory.Bass.NaturalTrack.Track L c F) :
    A.loops 0 = A := rfl
