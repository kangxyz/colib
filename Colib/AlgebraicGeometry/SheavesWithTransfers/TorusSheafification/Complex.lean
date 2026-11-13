/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The torus sheafification comparison on complexes

The chain map uses the original sheafification unit in every degree.
Exactness identifies the source homology with the torus sections of
the sheafified homology when the original homology is A¹-invariant.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k] {ι : Type w} (c : ComplexShape ι)

local notation "A" => nisnevichSheafify k
local notation "B" => torusSectionsFunctor k
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "T" => withParameterFunctor Gₘ
set_option quotPrecheck false in
local notation "aC" => (A).mapHomologicalComplex c
set_option quotPrecheck false in
local notation "bC" => (B).mapHomologicalComplex c
set_option quotPrecheck false in
local notation "tC" => (T).mapHomologicalComplex c

/-- Evaluate the actual sheafification comparison in every term of the
original complex. -/
def torusSectionsSheafificationComplexMap
    (K : HomologicalComplex (PresheafWithTransfers.{u + 1} k) c) :
    (aC).obj ((tC).obj K) ⟶ (bC).obj ((aC).obj K) where
  f i := torusSectionsSheafificationComparison k (K.X i)
  comm' i j _ := (torusSectionsSheafificationComparison_naturality k (K.d i j)).symm

/-- Each term extends the literal unit evaluated on the original torus. -/
@[reassoc (attr := simp)]
theorem torusSectionsSheafificationComplexMap_unit
    (K : HomologicalComplex (PresheafWithTransfers.{u + 1} k) c) (i : ι) :
    toNisnevichSheafify k (torusSections (K.X i)) ≫
      ((torusSectionsSheafificationComplexMap k c K).f i).hom =
        (T).map (toNisnevichSheafify k (K.X i)) :=
  torusSectionsSheafificationComparison_unit k (K.X i)

/-- Exact reindexing and sheafification give the original torus sections
of the sheafified homology in any A¹-invariant degree. -/
def torusSectionsSheafificationComplexHomologyIso
    (K : HomologicalComplex (PresheafWithTransfers.{u + 1} k) c) (i : ι)
    (h : (K.homology i).IsA1Invariant) :
    ((aC).obj ((tC).obj K)).homology i ≅ (B).obj (((aC).obj K).homology i) :=
  (((tC).obj K).sc i).mapHomologyIso A ≪≫
    (A).mapIso ((K.sc i).mapHomologyIso T) ≪≫
    torusSectionsSheafificationIso k (K.homology i) h ≪≫
    (B).mapIso ((K.sc i).mapHomologyIso A).symm

end AlgebraicGeometry.SheafWithTransfers
