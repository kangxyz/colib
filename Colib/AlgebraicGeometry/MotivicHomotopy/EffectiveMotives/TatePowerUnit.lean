/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusPowerRetract

/-!
# The torus unit on reduced powers

The degree-zero effective unit on a reduced transfer torus is tested
after the actual split quotient of its signed representable. The
original representable cancellation map descends on that quotient
to the original reduced parameter product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "D(" q ")" => Cor.mk (SmoothSite.torusPower Sₖ q)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "L" => effectiveReducedTorusTensorFunctor k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "B" => torusSectionsDerivedFunctor k
local notation "C" => singularEffectiveMotiveFunctor k
local notation "J" => effectiveMotivesMinusToDerived k
/-- Use the canonical abelian structure when interpreting the parameter unit. -/
local instance tatePowerUnitAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The original parameter product on the reduced torus motive, followed by
the genuine derived comparison for torus sections. -/
def reducedTorusDerivedParameterProduct (q : ℕ) :
    (J).obj ((C).obj (reducedTorus k q)) ⟶
      (B).obj ((J).obj ((C).obj (reducedTorus k (q + 1)))) :=
  DerivedCategory.Q.map
      ((singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q)) ≫
    singularSheafDerivedTorusSectionsMap k (reducedTorus k (q + 1))

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- Precomposition with the original split quotient identifies the
parameter product with the actual representable cancellation map. -/
theorem reducedTorusDerivedParameterProduct_quotient (q : ℕ) :
    let H : LargePresheaves k ⥤ DerivedCategory (LargeSheaves k) :=
      singularSheafCochainFunctor k 0 ⋙ DerivedCategory.Q
    H.map (toReducedTorus k q) ≫ reducedTorusDerivedParameterProduct k q =
      cancellationRepresentableDerivedMap k (D(q)) ≫
        (B).map (H.map (torusCancellationToReducedTorus k q)) := by
  intro H
  let P := reducedTorus k (q + 1)
  let Q := torusCancellationCoefficients k (D(q))
  let u := toReducedTorus k q
  let a := reducedTorusParameterProduct k q
  let b := torusCancellationParameterMap k (D(q))
  let f := torusCancellationToReducedTorus k q
  let v := withParameterMap f Gₘ
  let x := singularSheafDerivedTorusSectionsMap k P
  let y := singularSheafDerivedTorusSectionsMap k Q
  have hn : (H).map v ≫ x = y ≫ (B).map ((H).map f) :=
    singularSheafDerivedTorusSectionsMap_naturality k f
  rw [cancellationRepresentableDerivedMap_eq_parameterMap]
  change (H).map u ≫ (H).map a ≫ x = ((H).map b ≫ y) ≫ (B).map ((H).map f)
  calc
    _ = (H).map (u ≫ a) ≫ x := (Functor.map_comp_assoc (H) u a x).symm
    _ = (H).map (b ≫ v) ≫ x :=
      congrArg (fun m => (H).map m ≫ x) (reducedTorusParameterProduct_quotient k q)
    _ = (H).map b ≫ (H).map v ≫ x := Functor.map_comp_assoc (H) b v x
    _ = (H).map b ≫ y ≫ (B).map ((H).map f) := congrArg ((H).map b ≫ ·) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual effective unit on each reduced torus is the original
transferred parameter product, included into the full derived sections. -/
theorem effectiveReducedTorusTensorAdjunction_unit_app_torus (q : ℕ) :
    (J).map (((effectiveReducedTorusTensorAdjunction k).unit).app ((C).obj (reducedTorus k q)) ≫
        (R).map (effectiveReducedTorusTensorTorusRetractIso k q).hom) ≫
      (effectiveReducedTorusSectionsInclusion k).app ((C).obj (reducedTorus k (q + 1))) =
    reducedTorusDerivedParameterProduct k q := by
  let P := torusRepresentable k q
  let Q := reducedTorus k q
  let X := (C).obj P
  let Y := (C).obj Q
  let Y' := (C).obj (reducedTorus k (q + 1))
  let X' := (C).obj (torusCancellationCoefficients k (D(q)))
  let η := (effectiveReducedTorusTensorAdjunction k).unit
  let a := (C).map (toReducedTorus k q)
  let f := (C).map (torusCancellationToReducedTorus k q)
  let e := (effectiveReducedTorusTensorTorusRetractIso k q).hom
  let d := (effectiveReducedTorusTensorRepresentableIso k (D(q))).hom
  have h : (L).map a ≫ e = d ≫ f :=
    effectiveReducedTorusTensorTorusRetractIso_quotient k q
  let c := effectiveReducedTorusSectionsInclusion k
  let t := reducedTorusQuotientSection k q
  let F := (C) ⋙ J
  let s := F.map t.val
  let g := (J).map a
  have hs : s ≫ g = 𝟙 (F.obj Q) :=
    (F.map_comp t.val (toReducedTorus k q)).symm.trans
      ((F.congr_map t.property).trans (F.map_id Q))
  let : IsSplitEpi g := ⟨⟨⟨s, hs⟩⟩⟩
  let : Epi g := IsSplitEpi.epi g
  have he : a ≫ (η).app Y ≫ (R).map e =
      (effectiveMotiveReducedTorusIso k (D(q))).hom ≫ (R).map f := by
    calc
      _ = ((η).app X ≫ (R).map ((L).map a)) ≫ (R).map e :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (R).map e) ((η).naturality a))
      _ = (η).app X ≫ (R).map ((L).map a ≫ e) :=
        (Category.assoc _ _ _).trans (congrArg ((η).app X ≫ ·) ((R).map_comp _ _).symm)
      _ = (η).app X ≫ (R).map (d ≫ f) := congrArg (fun m => (η).app X ≫ (R).map m) h
      _ = ((η).app X ≫ (R).map d) ≫ (R).map f :=
        (congrArg ((η).app X ≫ ·) ((R).map_comp d f)).trans (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ (R).map f)
        (effectiveReducedTorusTensorAdjunction_unit_app_representable k (D(q)))
  have hn : (J).map ((R).map f) ≫ c.app Y' = c.app X' ≫ (B).map ((J).map f) :=
    c.naturality f
  apply (cancel_epi g).1
  calc
    _ = (J).map (a ≫ (η).app Y ≫ (R).map e) ≫ c.app Y' :=
      (Functor.map_comp_assoc (J) a ((η).app Y ≫ (R).map e) (c.app Y')).symm
    _ = (J).map ((effectiveMotiveReducedTorusIso k (D(q))).hom ≫ (R).map f) ≫ c.app Y' :=
      congrArg (fun m => (J).map m ≫ c.app Y') he
    _ = (J).map (effectiveMotiveReducedTorusIso k (D(q))).hom ≫
        (c.app X' ≫ (B).map ((J).map f)) := by
      rw [Functor.map_comp_assoc, hn]
    _ = cancellationRepresentableDerivedMap k (D(q)) ≫ (B).map ((J).map f) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (B).map ((J).map f))
          (effectiveMotiveReducedTorusIso_hom_inclusion k (D(q))))
    _ = _ := (reducedTorusDerivedParameterProduct_quotient k q).symm

end AlgebraicGeometry.MotivicHomotopy
