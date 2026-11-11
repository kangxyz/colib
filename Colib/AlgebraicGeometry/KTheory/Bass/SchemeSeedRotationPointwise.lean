/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedCospanIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeLoopConeTrackIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeLoopSeedFactor
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiPermutation
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedObjectIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeBassFunctorIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedEndpointIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeLoopConeSeedPointwiseIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality

/-!
# The pointwise finite Scheme seed rotation

The accepted whole geometric chi factorization, the original seed cospan, and the
fixed Bass-strength factorization imply the local base equation. The original inverse
loop transpose and the genuine two-cone geometric permutation remain explicit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology IteratedLoopStrength FiniteLoopWords
open GeometricConeInterchange LoopFactor
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

private theorem seed_factor_comp {D E : Type*} [Category* D] [Category* E]
    (L : D ⥤ E) {S T U : D} {V : E}
    {f : S ⟶ U} {g : S ⟶ T} {p : T ⟶ U}
    {a a' : V ⟶ L.obj S} {b : V ⟶ L.obj T} {d : V ⟶ L.obj U}
    (hχ : f = g ≫ p) (he : a' = a) (hs : a ≫ L.map f = d)
    (hc : a' ≫ L.map g = b) :
    d = b ≫ L.map p := by
  rw [← hs, ← he, hχ, L.map_comp, ← Category.assoc, hc]

private theorem loop_map_eq {E G : LoopPrespectrum.{w}} (f : E ⟶ G) :
    parameterLoopingFunctor.map f = parameterLoopingMap f := rfl

private theorem loop_obj_eq (E : LoopPrespectrum.{w}) :
    parameterLoopingFunctor.obj E = parameterLooping E := rfl

/-- The genuine two-cone permutation gives the exact finite rotation of the original seed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedRotationPointwise.lean:55"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem seed_cone_rotation_app_heq (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) :
    HEq (((strictDiagramFunctor squareFunctor).map (seed A) ≫
      strengthDiagram squareFunctor (iterate squareFunctor 1 F)).app X)
      ((Functor.whiskerRight (seed (coneTrack A 1)) parameterLoopingFunctor ≫
        (transposeIso (iterate squareFunctor 2 F)).inv ≫
        loopMap 2 (permutationNatIso F).hom).app X) := by
  have hs := GeometricSeedCospan.seed_cospan F A.homotopy A.naturality X
  rw [← seed_sourceTrack A] at hs
  have heapp := seed_loopCone_app_heq_bassSeed A X
  let s := (ConeTrack.diagram squareFunctor F).mapArrow.mapArrow.obj (square X)
  let V := mappingCone (StrictSquare.comparison s)
  let S := mappingCone (StrictSquare.comparison (loopSquare s))
  let T := parameterLooping V
  let U := parameterLooping V
  let p : V ⟶ V := by
    have hp := (permutation F X).hom
    dsimp only [coneFunctor_obj_obj_eq, coneFunctor_obj_eq] at hp
    exact hp
  let l : S ⟶ T := coneStrength s
  let q : T ⟶ U := parameterLoopingMap p
  have hχ := GeometricChiPermutation.comparison F X
  dsimp only [geometricSquare_coneDiagram_eq, coneDiagram_obj_eq,
    coneFunctor_obj_obj_eq, coneFunctor_obj_eq, bass_obj_eq, bass_square_eq] at hχ
  change _ = l ≫ q at hχ
  have hc := seed_loop_coneStrength (F := iterate squareFunctor 1 F) (coneTrack A 1) X
  dsimp only [geometricSquare_source_eq, geometricSquare_coneDiagram_eq,
    bassFunctor_obj_eq, loop_comp_obj_eq, coneDiagram_obj_eq,
    loop_comp_square_eq, iterate] at hs hc heapp
  have he := eq_of_heq heapp
  have hm := seed_factor_comp parameterLoopingFunctor
    (S := S) (T := T) (U := U) (g := l) (p := q) hχ he hs hc
  dsimp only [NatTrans.comp_app, strengthDiagram, transposeIso, NatIso.ofComponents,
    loopMap, Functor.whiskerRight_app, permutationNatIso]
  dsimp only [geometricSquare_source_eq, geometricSquare_coneDiagram_eq,
    bassFunctor_obj_eq, loop_comp_obj_eq, coneDiagram_obj_eq,
    loop_comp_square_eq, coneFunctor_obj_obj_eq, coneFunctor_obj_eq, iterate] at hm ⊢
  dsimp only [q, p, loop_map_eq] at hm ⊢
  dsimp only [U, T, V, S, s, loopDiagram, loop_comp_obj_eq, loop_obj_eq,
    coneDiagram_obj_eq, coneFunctor_obj_obj_eq, coneFunctor_obj_eq] at hm ⊢
  simp only [Category.assoc] at hm
  exact heq_of_eq hm

end KTheory.Bass.SchemeIteratedSeedTransition
