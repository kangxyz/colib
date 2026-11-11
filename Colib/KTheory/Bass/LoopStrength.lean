/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Reconstructed Bass loop strength

The original Bass action on the evaluation homotopy supplies a loop strength. This
independent reconstruction is adopted here and is not historical byte recovery.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.LoopStrength
variable {C : Type u} [Category.{v} C]

/-- Evaluation retains the original loop parameter as homotopy time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:28-37"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def evaluation (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    Homotopy (zeroHom (parameterLooping (F.obj X)) (F.obj X))
      (zeroHom (parameterLooping (F.obj X)) (F.obj X)) where
  level n := ⟨fun z => Path.toContinuousMap z.2 z.1, by fun_prop⟩
  at_zero n γ := γ.source
  at_one n γ := γ.target
  at_point n s := rfl
  comm n s γ t := rfl

/-- Evaluation is natural in every coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:38-51"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem evaluation_naturality (F : C ⥤ LoopPrespectrum.{w})
    {X Y : C} (f : X ⟶ Y) n r x :
    (F.map f).map n ((evaluation F X).level n (r, x)) =
      (evaluation F Y).level n
        (r, ((F ⋙ parameterLoopingFunctor).map f).map n x) := rfl

variable {E F : C ⥤ LoopPrespectrum.{w}}
    (H : ∀ X, Homotopy (zeroHom (E.obj X) (F.obj X))
      (zeroHom (E.obj X) (F.obj X)))
    (hH : ∀ {X Y} (f : X ⟶ Y) n r x,
      (F.map f).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (E.map f).map n x))

/-- The natural family of self-homotopies gives its original zero-loop map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:52-63"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def loopMap : E ⟶ F ⋙ parameterLoopingFunctor where
  app X := (H X).zeroLoopMap
  naturality {X Y} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    apply Path.ext
    funext r
    exact (hH f n r x).symm

/-- Apply the existing Bass homotopy and normalize only its zero endpoints. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:64-74"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def bassHomotopy (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    Homotopy
      (zeroHom (((strictDiagramFunctor Q).obj E).obj X)
        (((strictDiagramFunctor Q).obj F).obj X))
      (zeroHom (((strictDiagramFunctor Q).obj E).obj X)
        (((strictDiagramFunctor Q).obj F).obj X)) :=
  (strictDiagramMapHomotopy (η := diagramZeroMap E F) (θ := diagramZeroMap E F)
    H hH Q X).cast (strictDiagramFunctor_map_zero_app Q E F X)
      (strictDiagramFunctor_map_zero_app Q E F X)

/-- The entire Bass homotopy retains the original time-slice transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:75-83"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem bassHomotopy_apply (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ)
    (r : unitInterval) (x : (((strictDiagramFunctor Q).obj E).obj X).space n) :
    (bassHomotopy H hH Q X).level n (r, x) =
      (((strictDiagramFunctor Q).map (diagramHomotopyAt
        (η := diagramZeroMap E F) (θ := diagramZeroMap E F) H hH r)).app X).map n x := by
  exact congrArg (fun k => k.map n x) (strictDiagramMapHomotopy_at (η := diagramZeroMap E F)
    (θ := diagramZeroMap E F) H hH Q X r)

/-- The actual loop strength is the zero-loop map of Bass evaluation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:84-89"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def strength (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (((strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor)).obj X) ⟶
      parameterLooping (((strictDiagramFunctor Q).obj F).obj X) :=
  (bassHomotopy (evaluation F) (evaluation_naturality F) Q X).zeroLoopMap

/-- Evaluation of the original zero-loop map is the same time slice. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:90-104"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem loopMap_evaluation (r : unitInterval) :
    loopMap H hH ≫ diagramHomotopyAt
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (evaluation F) (evaluation_naturality F) r =
      diagramHomotopyAt (η := diagramZeroMap E F) (θ := diagramZeroMap E F) H hH r := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

/-- The actual strength commutes with zero-loop maps on all values. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrength.lean:105-126"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem strength_square (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    (((strictDiagramFunctor Q).map (loopMap H hH)).app X) ≫ strength Q F X =
      (bassHomotopy H hH Q X).zeroLoopMap := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext r
  have h := congrArg (fun η => (η.app X).map n x)
    ((strictDiagramFunctor Q).map_comp (loopMap H hH)
      (diagramHomotopyAt
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (evaluation F) (evaluation_naturality F) r))
  have he := congrArg (fun η => (((strictDiagramFunctor Q).map η).app X).map n x)
    (loopMap_evaluation H hH r)
  exact (bassHomotopy_apply (E := F ⋙ parameterLoopingFunctor) (F := F)
    (evaluation F) (evaluation_naturality F) Q X n r
    ((((strictDiagramFunctor Q).map (loopMap H hH)).app X).map n x)).trans
      (h.symm.trans (he.trans (bassHomotopy_apply H hH Q X n r x).symm))

end KTheory.Bass.LoopStrength
