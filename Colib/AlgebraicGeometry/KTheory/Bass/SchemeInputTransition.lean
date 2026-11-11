/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.FiniteTrackEquivariance
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope

/-! # Actual input maps preserve the current and normalized transitions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteConeTopology FiniteLoopWords AssociatedStrength
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (η : F ⟶ G) (hη : Equivariant A B η)

private theorem transport_inverse {C : Type*} [Category* C] {X X' Y Y' : C}
    (hx : X = X') (hy : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ eqToHom hy = eqToHom hx ≫ g) :
    g ≫ eqToHom hy.symm = eqToHom hx.symm ≫ f := by
  subst X'; subst Y'
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using h.symm

include hη

/-- A local whole-time input square preserves every literal current-stage seed transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTransition.lean:40"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem currentInput_transition (i : ℕ) :
    (strictDiagramIterate squareFunctor i).map η ≫ currentTransition B i =
      currentTransition A i ≫ (strictDiagramIterate squareFunctor (i + 1)).map η := by
  have hs := seed_square (stageTrack A i) (stageTrack B i)
    ((strictDiagramIterate squareFunctor i).map η)
    (hη.stages (L := laurent.op) (c := coefficient) squareFunctor
      (interchange (laurentProjection (.of (ULift.{u} ℤ))))
      (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i)
  have hc := transport_inverse (bass_succ_eq squareFunctor i F)
    (bass_succ_eq squareFunctor i G) _ _ (bass_succ_naturality squareFunctor i η)
  unfold currentTransition
  rw [← Category.assoc, ← hs, Category.assoc, hc, ← Category.assoc]

/-- The same input square preserves each original looped cone-seed transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTransition.lean:54"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem normalizedInput_transition (i : ℕ) :
    normalizedMap squareFunctor i η ≫ normalizedTransition B i =
      normalizedTransition A i ≫ normalizedMap squareFunctor (i + 1) η := by
  have hs := seed_square (coneTrack A i) (coneTrack B i) (iterateMap squareFunctor i η)
    (hη.cones (L := laurent.op) (c := coefficient) squareFunctor
      (interchange (laurentProjection (.of (ULift.{u} ℤ))))
      (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i)
  have hc := postcomp_naturality i (ConeTrack.map squareFunctor (iterateMap squareFunctor i η))
  unfold normalizedMap normalizedTransition
  rw [← Category.assoc, ← loopMap_comp, ← hs, loopMap_comp, Category.assoc]
  exact congrArg (fun k => loopMap i (seed (coneTrack A i)) ≫ k) hc

end KTheory.Bass.SchemeNaturalSeed
