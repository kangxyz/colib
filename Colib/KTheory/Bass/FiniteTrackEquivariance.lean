/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.NormalizedStageNaturality
public import Colib.KTheory.Bass.NormalizedStageAction

/-! # Original finite-stage maps preserve local whole-time equivariance -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.NaturalTrack
open FiniteConeTopology FiniteLoopWords NormalizedStageMap
variable {C : Type u} [Category.{v} C] {L : C ⥤ C} {c : 𝟭 C ⟶ L}
    {F G : C ⥤ LoopPrespectrum.{w}}

/-- Every original finite loop retains a given whole-time intertwining equation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteTrackEquivariance.lean:25"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem Equivariant.loops {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) (i : ℕ) :
    Equivariant (A.loops i) (B.loops i) (loopMap i η) := by
  induction i with
  | zero => exact hη
  | succ i ih => exact ih.loop

variable (Q : C ⥤ Arrow (Arrow C))
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Every original finite cone retains a given whole-time intertwining equation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteTrackEquivariance.lean:39"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem Equivariant.cones {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) (i : ℕ) :
    Equivariant (A.cones Q χ hχ i) (B.cones Q χ hχ i) (iterateMap Q i η) := by
  induction i with
  | zero => exact hη
  | succ i ih => exact ih.cone Q χ hχ

/-- The literal right-associated Bass-stage map retains the whole original action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteTrackEquivariance.lean:47"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem Equivariant.stages {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) (i : ℕ) :
    Equivariant (A.stages Q χ hχ i) (B.stages Q χ hχ i)
      ((strictDiagramIterate Q i).map η) := by
  induction i with
  | zero => exact hη
  | succ i ih =>
    have hm : eqToHom (bass_succ_eq Q i F) ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map η) ≫
          eqToHom (bass_succ_eq Q i G).symm = (strictDiagramIterate Q (i + 1)).map η := by
      rw [← bass_succ_naturality_assoc]
      simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hm]
    exact ((Equivariant.cast_source ((A.stages Q χ hχ i).bass Q χ hχ)
      (bass_succ_eq Q i F)).comp (ih.bass Q χ hχ)).comp
        (Equivariant.cast_target ((B.stages Q χ hχ i).bass Q χ hχ)
          (bass_succ_eq Q i G).symm)

end KTheory.Bass.NaturalTrack
