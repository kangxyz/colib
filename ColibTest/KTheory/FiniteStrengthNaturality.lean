module
import Colib.KTheory.Bass.NormalizedStageNaturality
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open KTheory.Bass Topology.LoopPrespectrum.FiniteLoopWords KTheory.Bass.NormalizedStageMap
open KTheory.Bass.FiniteLoopStrengthWords KTheory.Bass.IteratedLoopStrength
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
variable {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G)
example (j : ℕ) (t : Fin j → unitInterval) :
    (reversalIso j F).hom ≫ evaluationTuple j F t =
      evaluationTuple j F (t ∘ Fin.rev) := reversal_evaluationTuple j F t
example (j : ℕ) (t : Fin j → unitInterval) :
    loopMap j f ≫ evaluationTuple j G t = evaluationTuple j F t ≫ f :=
  IteratedStrengthNaturality.evaluationTuple_naturality j f t
example (i : ℕ) :
    (strictDiagramFunctor Q).map (loopMap i f) ≫ iteratedStrength Q i G =
      iteratedStrength Q i F ≫ loopMap i ((strictDiagramFunctor Q).map f) :=
  IteratedStrengthNaturality.iteratedStrength_naturality Q i f
example (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).map f ≫ eqToHom (bass_succ_eq Q i G) =
      eqToHom (bass_succ_eq Q i F) ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map f) :=
  bass_succ_naturality Q i f
example (i : ℕ) :
    (strictDiagramIterate Q i).map f ≫ stageMap Q i G =
      stageMap Q i F ≫ normalizedMap Q i f := stageMap_naturality Q i f
