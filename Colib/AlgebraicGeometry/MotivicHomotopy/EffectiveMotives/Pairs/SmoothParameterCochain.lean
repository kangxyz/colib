/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameterCone
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap
import Colib.Algebra.Homology.MappingCone.Augmentation

/-! # Smooth parameters on the original projective cochain pair -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance smoothParameterNaturalityAbelian : Abelian NST := SheafWithTransfers.abelian k
set_option quotPrecheck false in
local notation "a" => nisnevichSheafify k
local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "s" => CochainComplex.singleFunctor NST 0

variable {T : SmoothSite (Spec (CommRingCat.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)

set_option quotPrecheck false in
local notation "H" => coendPushforward F
set_option quotPrecheck false in
local notation "J" => (H ⋙ a)
set_option quotPrecheck false in
local notation "G" => parameterProduct T

set_option maxHeartbeats 750000 in
-- Compare the original graph square before its cone isomorphism is composed.
private theorem smoothParameterConeSquare {i j : Arrow Sm} (φ : i ⟶ j) :
    let f := (projectivePairCochain k).map φ
    let L := (J).mapHomologicalComplex c
    let v := smoothParameterTargetArrowMap (T := T) φ
    L.map f ≫ (smoothParameterCochainComparison e j).hom =
      (smoothParameterCochainComparison e i).hom ≫
        (smoothParameterTargetConeFunctor (k := k)).map v := by
  intro f L v
  let C := smoothParameterTargetConeFunctor (k := k)
  let m (b : Arrow Sm) := (smoothParameterConeMapIso (F := F) b).hom
  let d (b : Arrow Sm) := (smoothParameterCochainArrowIso e b).hom
  let u := smoothParameterSourceArrowMap φ
  let α := L.mapArrow.map u
  let B := CochainComplex.mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex PST ℤ))
  have hg : f = B.map u := rfl
  have hm : L.map f ≫ m j = m i ≫ C.map α :=
    (congrArg (fun z => L.map z ≫ m j) hg).trans
      (CochainComplex.SplitFactorization.coneMapIso_naturality_arrow J u)
  have hd : α ≫ d j = d i ≫ v := smoothParameterCochainArrowIso_naturality e φ
  rw [smoothParameterCochainComparison_hom e j, smoothParameterCochainComparison_hom e i]
  exact CochainComplex.SplitFactorization.comp_map_of_commSq C α v (d i) (d j)
    (L.map f) (m i) (m j) hd hm

set_option maxHeartbeats 1200000 in
-- Identify the already checked square with the maps of the original pairs.
/-- The cochain model of the fixed smooth parameter is natural on actual pairs. -/
theorem smoothParameterCochainComparison_naturality {i j : Arrow Sm} (φ : i ⟶ j) :
    let f := ((J).mapHomologicalComplex c).map ((projectivePairCochain k).map φ)
    let g := cochainTransferPairConeMap k ((G).mapArrow.map φ)
    f ≫ (smoothParameterCochainComparison e j).hom =
      (smoothParameterCochainComparison e i).hom ≫ g := by
  intro f g
  exact smoothParameterConeSquare e φ

/-- The cochain comparison followed by the quotient augmentation of the product pair. -/
def smoothParameterCochainAugmentation (j : Arrow Sm) :
    ((J).mapHomologicalComplex c).obj ((projectivePairCochain k).obj j) ⟶
      (s).obj ((transferPairCokernelFunctor k).obj ((G).mapArrow.obj j)) :=
  (smoothParameterCochainComparison e j).hom ≫
    CochainComplex.mappingCone.descShortComplex (cochainTransferPair k ((G).mapArrow.obj j))

set_option maxHeartbeats 750000 in
-- Use the right inclusion of the literal projective cone.
private theorem smoothParameterCochainAugmentation_inr (j : Arrow Sm) :
    ((J).mapHomologicalComplex c).map (CochainComplex.mappingCone.inr
      ((projectivePairArrow k).app j)) ≫ smoothParameterCochainAugmentation e j =
    (smoothParameterCochainEndpointIso e j.right).hom ≫
      (cochainTransferPair k ((G).mapArrow.obj j)).g := by
  let A := smoothParameterSourceArrow (k := k) j
  let B := cochainTransferPair k ((G).mapArrow.obj j)
  let d := (smoothParameterCochainArrowIso e j).hom
  let i := ((J).mapHomologicalComplex c).map (CochainComplex.mappingCone.inr A.hom)
  change i ≫ ((smoothParameterCochainComparison e j).hom ≫
    CochainComplex.mappingCone.descShortComplex B) = _
  rw [smoothParameterCochainComparison_hom e j, Category.assoc]
  exact CochainComplex.mappingCone.coneAugmentation_inr J A B d

section ParameterMap

variable {T' : SmoothSite (Spec (CommRingCat.of k))} {F' : Cor k ⥤ Cor k} [F'.Additive]
  (e' : Cor.graphFunctor k ⋙ F' ≅ parameterProduct T' ⋙ Cor.graphFunctor k)
  (g : T ⟶ T') (η : F ⟶ F')
  (hη : ∀ X : SmoothSite (Spec (CommRingCat.of k)), η.app (Cor.mk X) ≫ e'.hom.app X =
    e.hom.app X ≫ (Cor.graphFunctor k).map ((parameterMap g).app X))

set_option maxHeartbeats 950000 in
-- Check the quotient map on the original right endpoint in degree zero.
include hη in
/-- The cochain augmentation sends a parameter change to the actual map of quotients. -/
theorem smoothParameterCochainAugmentation_parameter (j : Arrow Sm) :
    let f := ((Functor.whiskerRight (coendPushforwardParameterMap η) a).mapHomologicalComplex c).app
      ((projectivePairCochain k).obj j)
    let r := (s).map ((transferPairCokernelFunctor k).map (smoothParameterArrowMap g j))
    f ≫ smoothParameterCochainAugmentation e' j =
      smoothParameterCochainAugmentation e j ≫ r := by
  intro f r
  let A := smoothParameterSourceArrow (k := k) j
  let B := cochainTransferPair k ((G).mapArrow.obj j)
  let B' := cochainTransferPair k ((parameterProduct T').mapArrow.obj j)
  let v : B ⟶ B' := (s).mapShortComplex.map
    (transferPairSequenceMap k (smoothParameterArrowMap g j))
  let i := CochainComplex.mappingCone.inr A.hom
  let τ := (Functor.whiskerRight (coendPushforwardParameterMap η) a).mapHomologicalComplex c
  let L := (J).mapHomologicalComplex c
  let L' := (coendPushforward F' ⋙ a).mapHomologicalComplex c
  let p := smoothParameterCochainAugmentation e j
  let p' := smoothParameterCochainAugmentation e' j
  let d := (smoothParameterCochainEndpointIso e j.right).hom
  let d' := (smoothParameterCochainEndpointIso e' j.right).hom
  have hz : IsZero (A.left.X 1) :=
    HomologicalComplex.isZero_single_obj_X c (0 : ℤ)
      ((representableLarge k).obj (Cor.mk j.left)) 1 (by decide)
  have hn : L.map i ≫ f = τ.app A.right ≫ L'.map i := τ.naturality i
  have hi : L.map i ≫ p = d ≫ B.g := smoothParameterCochainAugmentation_inr e j
  have hi' : L'.map i ≫ p' = d' ≫ B'.g := smoothParameterCochainAugmentation_inr e' j
  have he : τ.app A.right ≫ d' = d ≫ v.τ₂ :=
    smoothParameterCochainEndpointIso_parameter e e' g η hη j.right
  have hv : v.τ₂ ≫ B'.g = B.g ≫ r := v.comm₂₃
  apply CochainComplex.mappingCone.hom_ext_mapCone_to_single J A.hom hz
    ((transferPairCokernelFunctor k).obj ((parameterProduct T').mapArrow.obj j))
  calc
    _ = (L.map i ≫ f) ≫ p' := (Category.assoc _ _ _).symm
    _ = (τ.app A.right ≫ L'.map i) ≫ p' := congrArg (· ≫ p') hn
    _ = τ.app A.right ≫ (d' ≫ B'.g) :=
      (Category.assoc _ _ _).trans (congrArg (τ.app A.right ≫ ·) hi')
    _ = (d ≫ v.τ₂) ≫ B'.g := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ B'.g) he)
    _ = d ≫ (B.g ≫ r) := (Category.assoc _ _ _).trans (congrArg (d ≫ ·) hv)
    _ = (L.map i ≫ p) ≫ r := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) hi.symm)
    _ = _ := Category.assoc _ _ _

end ParameterMap

end AlgebraicGeometry.MotivicHomotopy
