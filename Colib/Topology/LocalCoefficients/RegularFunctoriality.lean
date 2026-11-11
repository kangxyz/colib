/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RegularChains

/-!
# Functoriality of regular chains along the original continuous map

The coefficient morphism maps actual path classes. Its composite with the
existing pushforward is the genuine regular chain map. An explicit equality
of basepoints is retained, so a commuting covering square does not have to
identify its corner points definitionally.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Convexity Opposite
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Apply the original continuous map to every basis path in the regular system. -/
def regularMap (f : C(X, Y)) (b : X) : regular b ⟶ pullback f (regular (f b)) where
  app x := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (fun q ↦
    (FundamentalGroupoid.map f).map q))
  naturality x y q := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro r z
    change Finsupp.mapDomain (fun t ↦ (FundamentalGroupoid.map f).map t)
        (Finsupp.mapDomain (fun t ↦ t ≫ q) (Finsupp.single r z)) =
      Finsupp.mapDomain (fun t ↦ t ≫ (FundamentalGroupoid.map f).map q)
        (Finsupp.mapDomain (fun t ↦ (FundamentalGroupoid.map f).map t) (Finsupp.single r z))
    simp only [Finsupp.mapDomain_single]
    exact congrArg (fun t ↦ Finsupp.single t z) ((FundamentalGroupoid.map f).map_comp r q)

/-- The coefficient map retains the actual image of the path class. -/
theorem regularMap_single (f : C(X, Y)) (b : X)
    {x : X} (q : Path.Homotopic.Quotient b x) (z : ℤ) :
    (regularMap f b).app (FundamentalGroupoid.mk x) (regularSingle b q z) =
      regularSingle (f b) (q.map f) z := by
  exact Finsupp.mapDomain_single

/-- The regular coefficient map with a specified equality at the target basepoint. -/
def regularMapTo (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    regular b ⟶ pullback f (regular b') :=
  regularMap f b ≫ eqToHom (congrArg (fun y ↦ pullback f (regular y)) hb.symm)

/-- A regular basis simplex under the original map, with its explicit basepoint cast. -/
def mapRegularSimplex (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    {n : SimplexCategory} (s : RegularSimplex b n) : RegularSimplex b' n :=
  ⟨f.comp s.1, (s.2.map f).cast hb rfl⟩

/-- The degreewise composite of the coefficient conversion and original pushforward. -/
def regularPushforwardModuleMap (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (n : SimplexCategory) : chainModule (regular b) n ⟶ chainModule (regular b') n :=
  coefficientModuleMap (regularMapTo f b b' hb) n ≫ pushforwardModuleMap f (regular b') n

/-- The actual coefficient-plus-spatial chain map on every regular generator. -/
@[simp]
theorem regularPushforwardModuleMap_generator (f : C(X, Y)) (b : X) (b' : Y)
    (hb : b' = f b) {n : SimplexCategory} (s : RegularSimplex b n) (z : ℤ) :
    regularPushforwardModuleMap f b b' hb n (regularChainGenerator b s z) =
      regularChainGenerator b' (mapRegularSimplex f b b' hb s) z := by
  subst b'
  change (chainInclusion (regular b) s.1 ≫
    regularPushforwardModuleMap f b (f b) rfl n) (regularSingle b s.2 z) = _
  dsimp only [regularPushforwardModuleMap, regularMapTo]
  simp only [eqToHom_refl, Category.comp_id]
  rw [chainInclusion_coefficientModuleMap_assoc]
  rw [chainInclusion_pushforwardModuleMap]
  change chainInclusion (regular (f b)) (f.comp s.1)
    ((regularMap f b).app _ (regularSingle b s.2 z)) = _
  rw [regularMap_single]
  simp only [regularChainGenerator, mapRegularSimplex, Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

/-- The actual simplicial map induced by a continuous map and explicit basepoint equality. -/
def regularPushforwardSimplicialMap (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    simplicialModule (regular b) ⟶ simplicialModule (regular b') :=
  coefficientSimplicialMap (regularMapTo f b b' hb) ≫
    pushforwardSimplicialMap f (regular b')

/-- The regular chain map is built from the already-defined original pushforward. -/
def regularPushforwardChainMap (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    singularChainComplex (regular b) ⟶ singularChainComplex (regular b') :=
  coefficientChainMap (regularMapTo f b b' hb) ≫ pushforwardChainMap f (regular b')

/-- Applying alternating faces gives precisely the displayed original-map composite. -/
theorem regularPushforwardChainMap_eq (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b) :
    regularPushforwardChainMap f b b' hb =
      (AlgebraicTopology.alternatingFaceMapComplex _).map
        (regularPushforwardSimplicialMap f b b' hb) := by
  simp [regularPushforwardChainMap, regularPushforwardSimplicialMap,
    coefficientChainMap, pushforwardChainMap]
  rfl

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:37-47"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMap

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:50-54"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMap_single

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:57-59"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMapTo

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:62-64"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  mapRegularSimplex

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:67-69"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularPushforwardModuleMap

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:73-87"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularPushforwardModuleMap_generator

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:90-93"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularPushforwardSimplicialMap

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:96-98"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularPushforwardChainMap

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RegularFunctoriality.lean:101-106"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularPushforwardChainMap_eq

end FundamentalGroupoid.LocalCoefficients
