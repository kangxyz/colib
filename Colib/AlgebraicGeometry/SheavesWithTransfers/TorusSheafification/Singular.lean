/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterSwap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Sheafification
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.Complex
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.HomotopyInvariance

/-!
# Torus sections and the original sheafified singular complex

The canonical chain map is the degreewise signed permutation followed
by sheafification on the actual product. Its source homology is the
original torus reindexing of singular homology after sheafification.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "T" => withParameterFunctor Gₘ
set_option quotPrecheck false in
local notation "A" => (nisnevichSheafify k).mapHomologicalComplex (ComplexShape.down ℕ)
local notation "B" => torusSectionsFunctor k

/-- Exchange the torus and simplex factors before applying the original
termwise sheafification comparison. -/
def singularSheafTorusSectionsMap (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafComplex k (torusSections P) ⟶
      ((B).mapHomologicalComplex (.down ℕ)).obj (singularSheafComplex k P) :=
  (A).map (withParameterSingularComplexIso P Gₘ).inv ≫
    torusSectionsSheafificationComplexMap k (.down ℕ) (singularComplex P)

/-- The chain comparison is pinned by the signed permutation and the actual
sheafification unit on the original torus product. -/
@[reassoc]
theorem singularSheafTorusSectionsMap_unit (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    toNisnevichSheafify k ((singularComplex (torusSections P)).X n) ≫
        ((singularSheafTorusSectionsMap k P).f n).hom =
      (withParameterSingularComplexIso P Gₘ).inv.f n ≫
        (T).map (toNisnevichSheafify k ((singularComplex P).X n)) := by
  change toNisnevichSheafify k ((singularComplex (torusSections P)).X n) ≫
      (((nisnevichSheafify k).map ((withParameterSingularComplexIso P Gₘ).inv.f n)).hom ≫
        ((torusSectionsSheafificationComplexMap k (.down ℕ) (singularComplex P)).f n).hom) = _
  rw [← Category.assoc, ← toNisnevichSheafify_naturality k, Category.assoc]
  let σ : (singularComplex (torusSections P)).X n ⟶ torusSections ((singularComplex P).X n) :=
    (withParameterSingularComplexIso P Gₘ).inv.f n
  change σ ≫ (toNisnevichSheafify k (torusSections ((singularComplex P).X n)) ≫
      ((torusSectionsSheafificationComplexMap k (.down ℕ) (singularComplex P)).f n).hom) =
    σ ≫ (T).map (toNisnevichSheafify k ((singularComplex P).X n))
  exact congrArg (σ ≫ ·) (torusSectionsSheafificationComplexMap_unit k (.down ℕ)
    (singularComplex P) n)

/-- On the original singular homology sheaves, the canonical comparison
identifies the source with torus reindexing in every degree. -/
def singularSheafTorusSectionsHomologyIso (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    (singularSheafComplex k (torusSections P)).homology n ≅
      (B).obj ((singularSheafComplex k P).homology n) :=
  (HomologicalComplex.homologyFunctor _ (.down ℕ) n).mapIso
      ((A).mapIso (withParameterSingularComplexIso P Gₘ).symm) ≪≫
    torusSectionsSheafificationComplexHomologyIso k (.down ℕ) (singularComplex P) n
      (singularComplex_homology_isA1Invariant P n)

end AlgebraicGeometry.SheafWithTransfers
