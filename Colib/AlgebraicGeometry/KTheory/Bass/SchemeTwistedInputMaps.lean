/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeWordNaturality

/-!
# Input naturality of the actual normalized-to-twisted telescope comparison

The original reversal and geometric words commute with every input diagram map.
A proved local action square therefore gives the actual twisted telescope input
map, and the original conjugacy commutes strictly with it on every cylinder.
All finite casts, transitions and cylinder heights remain unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteLoopWords FiniteConeTopology GeometricConeFixedWords
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The specified loop reversal and accumulated cone word are natural in the original input. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedInputMaps.lean:33"
  "adaptation" "Original actual twisted input map and complete conjugacy square."]
theorem conjugatingIso_naturality (i : ℕ) (η : F ⟶ G) :
    normalizedMap squareFunctor i η ≫ (conjugatingIso i G).hom =
      (conjugatingIso i F).hom ≫ normalizedMap squareFunctor i η := by
  have hr : loopMap i (iterateMap squareFunctor i η) ≫
      (reversalIso i (iterate squareFunctor i G)).hom =
    (reversalIso i (iterate squareFunctor i F)).hom ≫
      loopMap i (iterateMap squareFunctor i η) :=
    (reversal i).hom.naturality (iterateMap squareFunctor i η)
  rw [conjugatingIso_hom, conjugatingIso_hom]
  change loopMap i (iterateMap squareFunctor i η) ≫
      ((reversalIso i (iterate squareFunctor i G)).hom ≫ loopMap i (wordAt i G).hom) =
    ((reversalIso i (iterate squareFunctor i F)).hom ≫ loopMap i (wordAt i F).hom) ≫
      loopMap i (iterateMap squareFunctor i η)
  rw [← Category.assoc, hr, Category.assoc, ← loopMap_comp, wordAt_naturality,
    loopMap_comp, Category.assoc]

variable (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (η : F ⟶ G) (hη : Equivariant A B η)

include hη in
/-- The original normalized input maps preserve the prescribed twisted transitions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedInputMaps.lean:54"
  "adaptation" "Original actual twisted input map and complete conjugacy square."]
theorem twistedInput_transition (i : ℕ) :
    normalizedMap squareFunctor i η ≫ twistedTransition B i =
      twistedTransition A i ≫ normalizedMap squareFunctor (i + 1) η := by
  apply (cancel_epi (conjugatingIso i F).hom).1
  calc
    (conjugatingIso i F).hom ≫
        (normalizedMap squareFunctor i η ≫ twistedTransition B i) =
      normalizedMap squareFunctor i η ≫
        (normalizedTransition B i ≫ (conjugatingIso (i + 1) G).hom) := by
          rw [← Category.assoc, ← conjugatingIso_naturality, Category.assoc,
            ← twisted_adjacent]
    _ = normalizedTransition A i ≫
        (normalizedMap squareFunctor (i + 1) η ≫ (conjugatingIso (i + 1) G).hom) := by
          rw [← Category.assoc, normalizedInput_transition A B η hη, Category.assoc]
    _ = (conjugatingIso i F).hom ≫
        (twistedTransition A i ≫ normalizedMap squareFunctor (i + 1) η) := by
          rw [conjugatingIso_naturality, ← Category.assoc, twisted_adjacent, Category.assoc]

/-- The same finite looped cone maps descend through the original twisted telescope. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedInputMaps.lean:73"
  "adaptation" "Original actual twisted input map and complete conjugacy square."]
def twistedInputMap : twistedTelescope A ⟶ twistedTelescope B :=
  Telescope.diagramMap (fun i => normalized squareFunctor i F)
    (fun i => normalized squareFunctor i G) (twistedTransition A) (twistedTransition B)
    (fun i => normalizedMap squareFunctor i η) (twistedInput_transition A B η hη)

/-- The twisted input map keeps every original stage and entire cylinder height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedInputMaps.lean:79"
  "adaptation" "Original actual twisted input map and complete conjugacy square."]
theorem twistedInputMap_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : ((normalized squareFunctor i F).obj X).space n) :
    ((twistedInputMap A B η hη).app X).map n
      (Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (twistedTransition A j).app X) n i (s, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
        (fun j => (twistedTransition B j).app X) n i
        (s, ((normalizedMap squareFunctor i η).app X).map n x) := rfl

/-- Original stage inclusions commute with this actual twisted input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedInputMaps.lean:89"
  "adaptation" "Original actual twisted input map and complete conjugacy square."]
theorem twistedInputMap_inclusion (i : ℕ) :
    Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
        (twistedTransition A) i ≫ twistedInputMap A B η hη =
      normalizedMap squareFunctor i η ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j G)
          (twistedTransition B) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The actual normalized-to-twisted comparison commutes with every equivariant input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedInputMaps.lean:98"
  "adaptation" "Original actual twisted input map and complete conjugacy square."]
theorem conjugacyTelescopeMap_input_square :
    normalizedInputMap A B η hη ≫ conjugacyTelescopeMap B =
      conjugacyTelescopeMap A ≫ twistedInputMap A B η hη := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i s x
  change Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
      (fun j => (twistedTransition B j).app X) n i
      (s, ((conjugatingIso i G).hom.app X).map n
        (((normalizedMap squareFunctor i η).app X).map n x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
      (fun j => (twistedTransition B j).app X) n i
      (s, ((normalizedMap squareFunctor i η).app X).map n
        (((conjugatingIso i F).hom.app X).map n x))
  exact congrArg (fun y => Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
    (fun j => (twistedTransition B j).app X) n i (s, y))
      (congrArg (fun t => (t.app X).map n x) (conjugatingIso_naturality i η))

end KTheory.Bass.SchemeNaturalSeed
