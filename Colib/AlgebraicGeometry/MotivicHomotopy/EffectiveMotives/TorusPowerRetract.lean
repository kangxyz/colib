/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.RepresentableTorusUnit
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusProjector

/-!
# The effective torus tensor on reduced powers by retraction

The literal quotient and section of a transfer torus form a retract
on its singular motive. The corresponding target-unit quotient has
the same projector on its original parameter coordinate. The
representable effective comparison identifies the two retracts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "D(" q ")" => Cor.mk (SmoothSite.torusPower (Spec (CommRingCat.of k)) q)
local notation "L" => effectiveReducedTorusTensorFunctor k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "C" => singularEffectiveMotiveFunctor k

/-- The original effective tensor comparison commutes with the actual
signed projector on the representing torus. -/
theorem effectiveReducedTorusTensorRepresentableIso_projector (q : ℕ) :
    (L).map ((effectiveMotive k).map (reducedTorusProjector k q)) ≫
        (effectiveReducedTorusTensorRepresentableIso k (D(q))).hom =
      (effectiveReducedTorusTensorRepresentableIso k (D(q))).hom ≫
        (C).map (torusCancellationCoefficientsMap k (reducedTorusProjector k q)) := by
  let Y := D(q)
  let X := (effectiveMotive k).obj Y
  let T := (C).obj (torusCancellationCoefficients k Y)
  let a := reducedTorusProjector k q
  let f := (effectiveMotive k).map a
  let g := (C).map (torusCancellationCoefficientsMap k a)
  let e := (effectiveReducedTorusTensorRepresentableIso k Y).hom
  let j := (effectiveMotiveReducedTorusIso k Y).hom
  let A := effectiveReducedTorusTensorAdjunction k
  let η := A.unit
  have h : η.app X ≫ (R).map e = j :=
    effectiveReducedTorusTensorAdjunction_unit_app_representable k Y
  have hn : f ≫ j = j ≫ (R).map g :=
    effectiveMotiveReducedTorusIso_hom_naturality k a
  apply (A.homEquiv X T).injective
  change A.homEquiv X T ((L).map f ≫ e) = A.homEquiv X T (e ≫ g)
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  change f ≫ A.homEquiv X T e = A.homEquiv X T e ≫ (R).map g
  rw [A.homEquiv_unit]
  exact (congrArg (f ≫ ·) h).trans (hn.trans (congrArg (· ≫ (R).map g) h.symm))

/-- The effective tensor comparison on the actual reduced torus,
as the split image of the original representable comparison. -/
@[no_expose]
def effectiveReducedTorusTensorTorusRetractIso (q : ℕ) :
    (L).obj ((C).obj (reducedTorus k q)) ≅ (C).obj (reducedTorus k (q + 1)) := by
  let Y := D(q)
  let P := reducedTorus k q
  let Q := reducedTorus k (q + 1)
  let a := reducedTorusProjector k q
  let r := toReducedTorus k q
  let i := (reducedTorusQuotientSection k q).val
  let e := effectiveReducedTorusTensorRepresentableIso k Y
  let s := reducedTorusCancellationSection k q
  let t := torusCancellationToReducedTorus k q
  let p := (C).map (torusCancellationCoefficientsMap k a)
  let r' := (L).map ((C).map r)
  let i' := (L).map ((C).map i)
  let s' := (C).map s
  let t' := (C).map t
  let U := (C) ⋙ L
  have hp : (r' ≫ i') ≫ e.hom = e.hom ≫ p := by
    have h : r' ≫ i' = U.map ((representableLarge k).map a) :=
      (U.map_comp r i).symm.trans
        (U.congr_map (representableLarge_map_reducedTorusProjector k q).symm)
    exact (congrArg (· ≫ e.hom) h).trans
      (effectiveReducedTorusTensorRepresentableIso_projector k q)
  have hi : i' ≫ r' = 𝟙 (U.obj P) :=
    (U.map_comp i r).symm.trans
      ((U.congr_map (reducedTorusQuotientSection k q).property).trans (U.map_id P))
  have ht : s' ≫ t' = 𝟙 ((C).obj Q) := by
    rw [← (C).map_comp, reducedTorusCancellationSection_quotient, (C).map_id]
  have hs : t' ≫ s' = p :=
    ((C).map_comp t s).symm.trans ((C).congr_map (torusCancellationToReducedTorus_section k q))
  have hj : e.hom ≫ p ≫ e.inv = r' ≫ i' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e.inv) hp.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg ((r' ≫ i') ≫ ·) e.hom_inv_id).trans (Category.comp_id (r' ≫ i')))))
  have hj' : e.inv ≫ (r' ≫ i') ≫ e.hom = p :=
    (congrArg (e.inv ≫ ·) hp).trans (e.inv_hom_id_assoc _)
  refine
    { hom := i' ≫ e.hom ≫ t'
      inv := s' ≫ e.inv ≫ r'
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · calc
      _ = i' ≫ e.hom ≫ (t' ≫ s') ≫ e.inv ≫ r' := by simp only [Category.assoc]
      _ = i' ≫ (e.hom ≫ p ≫ e.inv) ≫ r' := by rw [hs]; simp only [Category.assoc]
      _ = _ := by
        rw [hj]
        simp only [Category.assoc, reassoc_of% hi, hi]
        exact Category.id_comp (𝟙 (U.obj P))
  · calc
      _ = s' ≫ (e.inv ≫ (r' ≫ i') ≫ e.hom) ≫ t' := by simp only [Category.assoc]
      _ = s' ≫ (t' ≫ s') ≫ t' := by rw [hj', ← hs]
      _ = _ := by
        simp only [Category.assoc, reassoc_of% ht, ht]
        exact Category.id_comp (𝟙 ((C).obj Q))

/-- The comparison on the split quotient retains the original
representable effective comparison. -/
@[reassoc]
theorem effectiveReducedTorusTensorTorusRetractIso_quotient (q : ℕ) :
    (L).map ((C).map (toReducedTorus k q)) ≫
        (effectiveReducedTorusTensorTorusRetractIso k q).hom =
      (effectiveReducedTorusTensorRepresentableIso k (D(q))).hom ≫
        (C).map (torusCancellationToReducedTorus k q) := by
  let Y := D(q)
  let e := (effectiveReducedTorusTensorRepresentableIso k Y).hom
  let r := toReducedTorus k q
  let i := (reducedTorusQuotientSection k q).val
  let t := torusCancellationToReducedTorus k q
  unfold effectiveReducedTorusTensorTorusRetractIso
  change ((C) ⋙ L).map r ≫ ((C) ⋙ L).map i ≫ e ≫ (C).map t = e ≫ (C).map t
  let U := (C) ⋙ L
  let a := reducedTorusProjector k q
  have h : U.map r ≫ U.map i = U.map ((representableLarge k).map a) :=
    (U.map_comp r i).symm.trans
      (U.congr_map (representableLarge_map_reducedTorusProjector k q).symm)
  have h' : (C).map (torusCancellationCoefficientsMap k a) ≫ (C).map t = (C).map t := by
    rw [← (C).map_comp, ← torusCancellationToReducedTorus_section, Category.assoc,
      reducedTorusCancellationSection_quotient]
    exact (C).congr_map (Category.comp_id t)
  calc
    _ = U.map ((representableLarge k).map a) ≫ e ≫ (C).map t :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e ≫ (C).map t) h)
    _ = e ≫ (C).map (torusCancellationCoefficientsMap k a) ≫ (C).map t :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (C).map t)
          (effectiveReducedTorusTensorRepresentableIso_projector k q)).trans (Category.assoc _ _ _))
    _ = _ := congrArg (e ≫ ·) h'

end AlgebraicGeometry.MotivicHomotopy
