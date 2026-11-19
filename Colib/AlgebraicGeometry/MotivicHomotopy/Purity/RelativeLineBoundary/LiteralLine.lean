/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineBoundary.ReducedProjection
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineBoundary.WeightOne
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.TrivialThomPowerBasic

/-!
# The signed raw boundary of the native trivial line

For one coordinate, the old open complement is empty and the Laurent chart
is the actual punctured line. The positive quotient of its torus motive gives
the forward trivial-line Thom map under the raw localization boundary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

private theorem chart_projection {C : Type*} [Category* C] (T : C ⥤ C)
    {G W Q J A X : C} (e : G ≅ W) (p : W ⟶ Q) (b : J ≅ Q) (pₗ : G ⟶ J)
    (t : J ⟶ T.obj A) (r : G ⟶ T.obj X) (q : X ⟶ A) (s : A ⟶ X)
    (hq : q ≫ s = 𝟙 X) (hp : pₗ ≫ b.hom = e.hom ≫ p)
    (ht : pₗ ≫ t = r ≫ T.map q) :
    (p ≫ b.inv ≫ t) ≫ T.map s = e.inv ≫ r := by
  have hₗ : e.hom ≫ p ≫ b.inv = pₗ := by
    rw [← Category.assoc e.hom, ← hp, Category.assoc, b.hom_inv_id, Category.comp_id]
  let c := (p ≫ b.inv ≫ t) ≫ T.map s
  have hc : e.hom ≫ c = r := by
    change e.hom ≫ ((p ≫ b.inv ≫ t) ≫ T.map s) = _
    calc
      _ = ((e.hom ≫ p ≫ b.inv) ≫ t) ≫ T.map s := by simp only [Category.assoc]
      _ = (pₗ ≫ t) ≫ T.map s := congrArg (fun g => (g ≫ t) ≫ T.map s) hₗ
      _ = r ≫ T.map (q ≫ s) := by rw [ht, Category.assoc, ← T.map_comp]
      _ = _ := by rw [hq, T.map_id, Category.comp_id]
  exact e.eq_inv_comp.mpr hc

variable (k : Type u) [Field k]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))

local instance instNoetherianLiteralTrivialLine :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))

private theorem rankZeroComplement_isEmpty (X : Sm(k)) :
    IsEmpty ((opensFunctor X).obj (closedPairOpen (affineCylinderPowerZero k X 0).left)).left :=
  ⟨fun x => x.property ⟨x.val, rfl⟩⟩

/-- The open complement of the original rank-one zero section. -/
abbrev trivialLinePuncture (X : Sm(k)) :=
  closedPairOpenInclusion (appendZeroSection (.of k) (affineCylinderPowerZero k X 0)).left

set_option maxHeartbeats 650000 in
-- The other chart has empty source because it projects onto the old open complement.
private theorem isIso_trivialLineLaurentChart (X : Sm(k)) :
    IsIso (appendZeroLaurentOpen (.of k) (affineCylinderPowerZero k X 0)) := by
  let R := CommRingCat.of k
  let z := affineCylinderPowerZero k X 0
  let U := (opensFunctor X).obj (closedPairOpen z.left)
  let i := appendZeroAffineOpen R z
  let l := appendZeroLaurentOpen R z
  let p := (projection (SmoothSite.additiveGroupObject (Spec R))).app U
  have hU : IsEmpty U.left := rankZeroComplement_isEmpty k X
  have hi : Set.range i.left = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨y, _⟩
    exact @IsEmpty.false U.left hU (p.left y)
  have hr : Set.range l.left = Set.univ := by
    have h := appendZeroOpen_range_cover R z
    change Set.range i.left ∪ Set.range l.left = Set.univ at h
    simpa only [hi, Set.empty_union] using h
  let : IsIso ((forgetScheme (Spec R)).map l) := by
    change IsIso l.left
    apply AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top
    apply SetLike.coe_injective
    rw [AlgebraicGeometry.Scheme.Hom.coe_opensRange]
    exact hr
  exact isIso_of_reflects_iso l (forgetScheme (Spec R))

/-- For the literal trivial line the existing Laurent chart is an isomorphism
onto the original punctured open. -/
@[no_expose]
def trivialLineLaurentIso (X : Sm(k)) :
    torusCylinder.obj X ≅ (opensFunctor (affineLineCylinder.obj X)).obj
      (closedPairOpen (appendZeroSection (.of k) (affineCylinderPowerZero k X 0)).left) := by
  let := isIso_trivialLineLaurentChart k X
  exact asIso (appendZeroLaurentOpen (.of k) (affineCylinderPowerZero k X 0))

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

local notation "E(" K ")" => effectiveSmoothMotive K
local notation "T(" K ")" => effectiveReducedTorusTensorFunctor K

/-- The transfer-sheaf abelian structure for the literal trivial line calculation. -/
local instance instAbelianLiteralTrivialLine : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

/-- The actual reduced torus projection transported along the Laurent chart. -/
def trivialLineReducedCoordinate (X : Sm(k)) :
    (E(k)).obj ((opensFunctor (affineLineCylinder.obj X)).obj
      (closedPairOpen (appendZeroSection (.of k) (affineCylinderPowerZero k X 0)).left)) ⟶
      (T(k)).obj ((E(k)).obj X) :=
  (E(k)).map (trivialLineLaurentIso k X).inv ≫
    (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk X)).r

set_option Elab.async false in
set_option maxHeartbeats 2400000 in
-- Specialize the chart square at the original motive objects of the rank-zero quotient.
private theorem trivialLine_projection (X : Sm(k)) :
    let R := CommRingCat.of k
    let z := affineCylinderPowerZero k X 0
    let j := closedPairOpenInclusion z.left
    let i := appendZeroAffineOpen R z
    let l := appendZeroLaurentOpen R z
    let v := trivialLinePuncture k X
    let b := relativeLineLaurentComparison k j i l v
      (appendZeroAffineOpen_comp R z) (appendZeroLaurentOpen_comp R z)
      (appendZeroOpen_isPullback R z) (appendZeroOpen_range_cover R z)
    (effectivePairMotiveQuotient k i ≫ b.inv ≫ (effectiveRelativeLaurentRetract k j).r) ≫
        (T(k)).map (effectiveTrivialPowerThomIso k X 0).hom =
      trivialLineReducedCoordinate k X := by
  intro R z j i l v b
  let F := E(k)
  let T := T(k)
  let O := (opensFunctor (affineCylinderPower k X 0)).obj (closedPairOpen z.left)
  let : IsEmpty O.left := rankZeroComplement_isEmpty k X
  let q : F.obj X ⟶ effectivePairMotive k j := effectivePairMotiveQuotient k j
  let : IsIso q := isIso_effectivePairMotiveQuotient_of_isEmpty k (U := O) j
  let s : effectivePairMotive k j ⟶ F.obj X := (effectiveTrivialPowerThomIso k X 0).hom
  let b₀ : effectivePairMotive k (torusCylinder.map j) ≅ effectivePairMotive k i := b
  let r : F.obj (torusCylinder.obj X) ⟶ T.obj (F.obj X) :=
    (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk X)).r
  let t := (effectiveRelativeLaurentRetract k j).r
  let p := effectivePairMotiveQuotient k i
  let pₗ : F.obj (torusCylinder.obj X) ⟶ effectivePairMotive k (torusCylinder.map j) :=
    effectivePairMotiveQuotient k (torusCylinder.map j)
  let e := F.mapIso (trivialLineLaurentIso k X)
  have hq : q ≫ s = 𝟙 _ := by
    change q ≫ inv q = _
    exact IsIso.hom_inv_id q
  have hp : pₗ ≫ b₀.hom = e.hom ≫ p :=
    effectivePairMotiveQuotient_relativeLineLaurentComparison k j i l v
      (appendZeroAffineOpen_comp R z) (appendZeroLaurentOpen_comp R z)
      (appendZeroOpen_isPullback R z) (appendZeroOpen_range_cover R z)
  have ht : pₗ ≫ t = r ≫ T.map q := effectivePairMotiveQuotient_comp_reducedLaurentProjection k j
  exact chart_projection T e p b₀ pₗ t r q s hq hp ht

set_option maxHeartbeats 1600000 in
-- Keep the original successor and the shift of the same rank-zero quotient.
/-- The forward native trivial-line Thom map is the raw localization
boundary of the original punctured line applied to the original projection. -/
theorem effectiveTrivialLineThomIso_hom_raw_boundary (X : Sm(k)) :
    (effectiveTrivialPowerThomIso k X 1).hom =
      effectivePairBoundary k (trivialLinePuncture k X) ≫
        (trivialLineReducedCoordinate k X)⟦(1 : ℤ)⟧' := by
  let R := CommRingCat.of k
  let z := affineCylinderPowerZero k X 0
  let j := closedPairOpenInclusion z.left
  let i := appendZeroAffineOpen R z
  let l := appendZeroLaurentOpen R z
  let v := trivialLinePuncture k X
  let hi := appendZeroAffineOpen_comp R z
  let hl := appendZeroLaurentOpen_comp R z
  let hpb := appendZeroOpen_isPullback R z
  let hcov := appendZeroOpen_range_cover R z
  let b := relativeLineLaurentComparison k j i l v hi hl hpb hcov
  let p := effectivePairMotiveQuotient k i ≫ b.inv ≫ (effectiveRelativeLaurentRetract k j).r
  let e₀ := effectiveTrivialPowerThomIso k X 0
  let δ := effectivePairBoundary k v
  let H := shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)
  let f := (T(k)).map e₀.hom
  have hp : p ≫ f = trivialLineReducedCoordinate k X := trivialLine_projection k X
  have h : (relativeLineThomIso k j i l v hi hl hpb hcov).hom = δ ≫ H.map p :=
    relativeLineThomIso_hom_effectivePairBoundary k j i l v hi hl hpb hcov
  change (relativeLineThomIso k j i l v hi hl hpb hcov).hom ≫ H.map f =
    δ ≫ H.map (trivialLineReducedCoordinate k X)
  rw [h, Category.assoc, ← H.map_comp, hp]

set_option maxHeartbeats 650000 in
-- Evaluate the raw boundary in the already chosen forward Thom orientation.
/-- Under the native trivial-line Thom orientation, the raw boundary of
the reduced Laurent projection is the identity of the Lefschetz twist. -/
theorem effectiveTrivialLineBoundary_reducedCoordinate (X : Sm(k)) :
    (effectiveTrivialPowerThomIso k X 1).inv ≫
        effectivePairBoundary k (trivialLinePuncture k X) ≫
        (trivialLineReducedCoordinate k X)⟦(1 : ℤ)⟧' = 𝟙 _ := by
  rw [← effectiveTrivialLineThomIso_hom_raw_boundary]
  exact (effectiveTrivialPowerThomIso k X 1).inv_hom_id

set_option maxHeartbeats 850000 in
-- Identify the original product over the base with the original torus.
/-- Over the field point the transported projection uses the native torus
and its original positive reduced quotient. -/
theorem trivialLineReducedCoordinate_base :
    let B := SmoothSite.base (Spec (CommRingCat.of k))
    trivialLineReducedCoordinate k B =
      (E(k)).map ((trivialLineLaurentIso k B).inv ≫ (torusBaseProduct (k := k)).hom) ≫
        torusReducedProjection k := by
  intro B
  let F := E(k)
  let e := trivialLineLaurentIso k B
  let t := torusBaseProduct (k := k)
  let r := (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk B)).r
  have ht : F.map t.hom ≫ F.map t.inv = 𝟙 _ := by
    rw [← F.map_comp, t.hom_inv_id, F.map_id]
  change F.map e.inv ≫ r = F.map (e.inv ≫ t.hom) ≫ (F.map t.inv ≫ r)
  rw [F.map_comp, Category.assoc, ← Category.assoc (F.map t.hom), ht, Category.id_comp]

set_option maxHeartbeats 950000 in
-- Read the positive weight-one graph in the already fixed Thom orientation.
/-- The raw localization boundary of the forward Laurent graph is (+1)
under the native trivial-line Thom orientation at the field point. -/
theorem effectiveTrivialLineBoundary_laurentCoordinate :
    let B := SmoothSite.base (Spec (CommRingCat.of k))
    let a := (trivialLineLaurentIso k B).inv ≫ (torusBaseProduct (k := k)).hom
    let x := (E(k)).map a ≫ (singularEffectiveMotiveFunctor k).map
      (PresheafWithTransfers.torusCoordinateGraphQuotient k) ≫
        (effectiveReducedTorusWeightOneIso k).inv
    (effectiveTrivialPowerThomIso k B 1).inv ≫
        effectivePairBoundary k (trivialLinePuncture k B) ≫ x⟦(1 : ℤ)⟧' = 𝟙 _ := by
  intro B a x
  let e := effectiveReducedTorusWeightOneIso k
  let Q := singularEffectiveMotiveFunctor k
  let q : (E(k)).obj (multiplicativeGroupObject (Spec (CommRingCat.of k))) ⟶
      Q.obj (PresheafWithTransfers.reducedTorus k 1) :=
    Q.map (PresheafWithTransfers.torusCoordinateGraphQuotient k)
  have hq : q ≫ e.inv = torusReducedProjection k :=
    e.comp_inv_eq.mpr (torusReducedProjection_weightOne k).symm
  have hb : trivialLineReducedCoordinate k B = (E(k)).map a ≫ torusReducedProjection k :=
    trivialLineReducedCoordinate_base k
  have hx : x = trivialLineReducedCoordinate k B :=
    (congrArg ((E(k)).map a ≫ ·) hq).trans hb.symm
  rw [hx]
  exact effectiveTrivialLineBoundary_reducedCoordinate k B

end AlgebraicGeometry.MotivicHomotopy
