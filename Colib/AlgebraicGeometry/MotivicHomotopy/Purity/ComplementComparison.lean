/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair

/-! # Comparing open complements with the same range -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {U V X : SmoothSite S} (i : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion i.left] [IsOpenImmersion j.left] (h : Set.range i.left = Set.range j.left)

/-- Two inclusions of the same open define isomorphic arrows over the
original ambient scheme. -/
def openInclusionArrowIso : Arrow.mk i ≅ Arrow.mk j := by
  let e := IsOpenImmersion.isoOfRangeEq i.left j.left h
  have hi : e.hom ≫ j.left = i.left := IsOpenImmersion.isoOfRangeEq_hom_fac i.left j.left h
  have hj : e.inv ≫ i.left = j.left := IsOpenImmersion.isoOfRangeEq_inv_fac i.left j.left h
  let e' : U ≅ V :=
    { hom := homMk e.hom (by
        rw [← MorphismProperty.Over.w j, ← Category.assoc, hi, MorphismProperty.Over.w i])
      inv := homMk e.inv (by
        rw [← MorphismProperty.Over.w i, ← Category.assoc, hj, MorphismProperty.Over.w j])
      hom_inv_id := MorphismProperty.Over.Hom.ext e.hom_inv_id
      inv_hom_id := MorphismProperty.Over.Hom.ext e.inv_hom_id }
  exact Arrow.isoMk e' (Iso.refl X) (by
    have h' : e'.hom ≫ j = i := MorphismProperty.Over.Hom.ext hi
    exact h'.trans (Category.comp_id i).symm)

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The pair motive comparison between two presentations of the same
open complement comes from the original isomorphism of inclusions. -/
def effectivePairMotiveIsoOfRangeEq {U V X : SmoothSite (Spec (.of k))}
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (h : Set.range i.left = Set.range j.left) :
    effectivePairMotive k i ≅ effectivePairMotive k j :=
  (effectivePairMotiveFunctor k).mapIso (SmoothSite.openInclusionArrowIso i j h)

end AlgebraicGeometry.MotivicHomotopy
