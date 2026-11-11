/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionBaseChange
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionTower
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TupleFieldChange
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange

/-!
# Field change on reduced diagonal chains

Scalar pullback preserves the native identity-coordinate relations and gives
the map on the evaluated reduced torus. The zero-simplex comparison and
the scalar projection of a rational graph identify its point representatives.

Adapted from `Motivic/Cohomology/Diagonal/FieldChange.lean:59-69,116-137` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin
open scoped Simplicial

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers
open DiagonalTopDegree DiagonalFiniteCyclePushforward DiagonalReducedPushforward
open DiagonalCycleSymbols (rationalTuple cycleClass cycleClass_apply graphSymbol)
open DiagonalCorestriction DiagonalCorestrictionBaseChange

private theorem finiteCyclePushforward_congr_hom {A B : Scheme.{u}} (f g : A ⟶ B)
    [IsFinite f] [IsFinite g] (h : f = g) (c : AlgebraicCycle A ℤ) :
    finiteCyclePushforward f c = finiteCyclePushforward g c := by
  cases h
  rfl

private theorem baseChange_closed_support {X X' Y Y' : Scheme.{u}}
    (b : X ⟶ Y) (b' : X' ⟶ Y') [IsClosedImmersion b] [IsClosedImmersion b']
    (m : X' ⟶ X) (n : Y' ⟶ Y) (sq : IsPullback m b' b n) (z : X)
    [IsNoetherian (pullback (integralComponentAt z).subschemeι m : Scheme.{u})]
    [IsNoetherian (pullback (integralComponentAt (b z)).subschemeι n : Scheme.{u})] :
    finiteCyclePushforward b'
      (finiteCyclePushforward (pullback.snd (integralComponentAt z).subschemeι m)
        (AlgebraicCycle.fundamentalCycle (pullback (integralComponentAt z).subschemeι m))) =
      finiteCyclePushforward (pullback.snd (integralComponentAt (b z)).subschemeι n)
        (AlgebraicCycle.fundamentalCycle (pullback (integralComponentAt (b z)).subschemeι n)) := by
  let i := (integralComponentAt z).subschemeι
  let j := (integralComponentAt (b z)).subschemeι
  have hker : (i ≫ b).ker = j.ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, map_integralComponentAt]
  obtain ⟨e, he⟩ := exists_iso_of_ker_eq (i ≫ b) j hker
  let hp := (IsPullback.of_hasPullback i m).paste_vert sq
  let t := pullback.map (i ≫ b) n j n e.hom (𝟙 Y') (𝟙 Y)
    ((Category.comp_id _).trans he.symm) (by simp)
  let : IsIso t := pullback.map_isIso _ _ _ _ _ _ _ _ _
  let e' := hp.isoPullback ≪≫ asIso t
  have hmap : e'.hom ≫ pullback.snd j n = pullback.snd i m ≫ b' := by
    change hp.isoPullback.hom ≫ t ≫ pullback.snd j n = _
    have h : t ≫ pullback.snd j n = pullback.snd (i ≫ b) n :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    rw [h]
    exact hp.isoPullback_hom_snd
  rw [finiteCyclePushforward_comp_apply,
    finiteCyclePushforward_congr_hom _ _ hmap.symm, ← finiteCyclePushforward_comp_apply,
    finiteCyclePushforward_fundamentalCycle_iso]

section Algebra

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private theorem cyclePullback_axis (r : Fin 2) (q : ℕ) (i : Fin (q + 1))
    (α : Cor.mk (source k r) ⟶ Cor.mk (target k q)) :
    cyclePullback (k := k) (L := L) r (q + 1)
      (α ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) q i)) =
      cyclePullback (k := k) (L := L) r q α ≫
        (Cor.graphFunctor L).map (SmoothSite.torusInsertOne (Spec (.of L)) q i) := by
  let a := SmoothSite.torusInsertOne (Spec (.of k)) q i
  let a' := SmoothSite.torusInsertOne (Spec (.of L)) q i
  let F := (cyclePullback (k := k) (L := L) r (q + 1)).comp
    (Preadditive.rightComp (Cor.mk (source k r)) ((Cor.graphFunctor k).map a))
  let G := (Preadditive.rightComp (Cor.mk (source L r)) ((Cor.graphFunctor L).map a')).comp
    (cyclePullback (k := k) (L := L) r q)
  have h : F = G := by
    apply finiteCorrespondences.addHom_ext_one (source k r).hom (target k q).hom
    intro z hz
    let b := axisMap k r q i
    let b' := axisMap L r q i
    let y := b z
    let m := ambientMap (k := k) (E := L) r q
    let n := ambientMap (k := k) (E := L) r (q + 1)
    have hb : b ≫ pullback.fst (source k r).hom (target k (q + 1)).hom =
        pullback.fst (source k r).hom (target k q).hom :=
      Cor.graphTargetMap_fst k (source k r) a
    have hy : IsFiniteCorrespondencePoint (source k r).hom (target k (q + 1)).hom y := by
      apply isFiniteCorrespondencePoint_finiteMap _ _ b z
      · rw [Category.assoc, hb]
        exact hz.1
      · rw [Category.assoc, hb]
        exact hz.2
    have hprime : singleFiniteCorrespondence (source k r).hom (target k q).hom z hz 1 ≫
        (Cor.graphFunctor k).map a =
        singleFiniteCorrespondence (source k r).hom (target k (q + 1)).hom y hy 1 := by
      apply Subtype.ext
      rw [Cor.comp_graph_val_of_finite]
      exact finiteCyclePushforward_single_of_isClosedImmersion b z 1
    have sq : IsPullback m b' b n := by
      apply IsPullback.of_bot (t := ambientMap_isPullback (k := k) (E := L) r (q + 1))
      · simpa only [b, b', axisMap, ← Category.assoc, Cor.graphTargetMap_fst] using
          (ambientMap_isPullback (k := k) (E := L) r q)
      · exact (ambientMap_axis (k := k) (E := L) r q i).symm
    apply Subtype.ext
    change (cyclePullback (k := k) (L := L) r (q + 1)
        (singleFiniteCorrespondence _ _ z hz 1 ≫ (Cor.graphFunctor k).map a)).val =
      (cyclePullback (k := k) (L := L) r q (singleFiniteCorrespondence _ _ z hz 1) ≫
        (Cor.graphFunctor L).map a').val
    rw [hprime, cyclePullback_single, cyclePullback_single,
      Cor.comp_graph_val_of_finite, supportPullbackCycle_val, supportPullbackCycle_val]
    let : IsNoetherian (ambient L r q) :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (simplexAmbientStructure L r q)
    let : IsNoetherian (ambient L r (q + 1)) :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (simplexAmbientStructure L r (q + 1))
    let : IsNoetherian (pullback (integralComponentAt z).subschemeι m : Scheme.{u}) :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (pullback.snd _ _)
    let : IsNoetherian (pullback (integralComponentAt (b z)).subschemeι n : Scheme.{u}) :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (pullback.snd _ _)
    exact (baseChange_closed_support b b' m n sq z).symm
  exact DFunLike.congr_fun h α

private def zeroCycleToPoint (F : Type u) [Field F] (q : ℕ) :
    (Cor.mk (source F 0) ⟶ Cor.mk (target F q)) →+
      (point F ⟶ DiagonalCycleSymbols.target F q) :=
  Preadditive.leftComp _ ((Cor.graphFunctor F).map (zeroSourceIso F).inv)

private theorem zeroCycleToPoint_val (F : Type u) [Field F] (q : ℕ)
    (α : Cor.mk (source F 0) ⟶ Cor.mk (target F q)) :
    (zeroCycleToPoint F q α).val = finiteCyclePushforward (zeroAmbientProjection F q) α.val := by
  let e := (Cor.graphFunctor F).mapIso (zeroSourceIso F)
  have h := zeroProjection_cycle F q (zeroCycleToPoint F q α)
  change finiteCyclePushforward (zeroAmbientProjection F q) (e.hom ≫ e.inv ≫ α).val =
    (zeroCycleToPoint F q α).val at h
  rw [Iso.hom_inv_id_assoc] at h
  exact h.symm

private theorem zeroCycleToPoint_precomp (F : Type u) [Field F] (q : ℕ)
    (α : point F ⟶ DiagonalCycleSymbols.target F q) :
    zeroCycleToPoint F q (WeightOne.zeroSimplexProjection F ≫ α) = α := by
  let e := (Cor.graphFunctor F).mapIso (zeroSourceIso F)
  change e.inv ≫ e.hom ≫ α = α
  exact e.inv_hom_id_assoc α

private theorem pointCycleFieldChange_zeroCycleToPoint (q : ℕ) :
    (pointCycleFieldChange (k := k) (L := L) q).comp (zeroCycleToPoint k q) =
      (zeroCycleToPoint L q).comp (cyclePullback (k := k) (L := L) 0 q) := by
  classical
  apply finiteCorrespondences.addHom_ext_one (source k 0).hom (target k q).hom
  intro z hz
  let b := zeroAmbientProjection k q
  let b' := zeroAmbientProjection L q
  let m := ambientMap (k := k) (E := L) 0 q
  let n := pointAmbientMap (k := k) (E := L) q
  let α := singleFiniteCorrespondence (source k 0).hom (target k q).hom z hz 1
  have hv : (zeroCycleToPoint k q α).val = single (b z) 1 :=
    (zeroCycleToPoint_val k q α).trans (finiteCyclePushforward_single_of_isClosedImmersion b z 1)
  have hy : IsFiniteCorrespondencePoint (SmoothSite.base (Spec (.of k))).hom (target k q).hom
      (b z) := (zeroCycleToPoint k q α).property.2 _ (by
    change (zeroCycleToPoint k q α).val (b z) ≠ 0
    rw [hv, single_apply, ite_eq_left rfl]
    exact one_ne_zero)
  have hα : zeroCycleToPoint k q α = singleFiniteCorrespondence _ _ (b z) hy 1 :=
    Subtype.ext hv
  apply Subtype.ext
  change (pointCycleFieldChange (k := k) (L := L) q (zeroCycleToPoint k q α)).val =
    (zeroCycleToPoint L q (cyclePullback (k := k) (L := L) 0 q α)).val
  rw [hα, zeroCycleToPoint_val]
  change _ = finiteCyclePushforward b' (cyclePullback (k := k) (L := L) 0 q
    (singleFiniteCorrespondence _ _ z hz 1)).val
  rw [cyclePullback_single, supportPullbackCycle_val]
  let : IsNoetherian (ambient L 0 q) :=
    isNoetherian_of_quasiCompact_locallyOfFiniteType (simplexAmbientStructure L 0 q)
  let : IsNoetherian (pointAmbient L q) :=
    isNoetherian_of_quasiCompact_locallyOfFiniteType (pointAmbientStructure L q)
  let : IsNoetherian (pullback (integralComponentAt z).subschemeι m : Scheme.{u}) :=
    isNoetherian_of_quasiCompact_locallyOfFiniteType (pullback.snd _ _)
  let : IsNoetherian (pullback (integralComponentAt (b z)).subschemeι n : Scheme.{u}) :=
    isNoetherian_of_quasiCompact_locallyOfFiniteType (pullback.snd _ _)
  let sq := pointAmbientMap_isPullback (k := k) (L := L) q
  let g : (target k q).left ⟶ Spec (.of k) := (target k q).hom
  let g' : (target L q).left ⟶ Spec (.of L) := (target L q).hom
  have hc := cyclePullbackAlong_single (f := 𝟙 (Spec (.of k))) (g := g)
    (f' := 𝟙 (Spec (.of L))) (g' := g') sq
    (fun y _ => pointSupport_flat k q y) (b z) hy
  have hval :
      (pointCycleFieldChange (k := k) (L := L) q
        (singleFiniteCorrespondence _ _ (b z) hy 1)).val =
      finiteCyclePushforward (pullback.snd (integralComponentAt (b z)).subschemeι n)
        (AlgebraicCycle.fundamentalCycle (pullback (integralComponentAt (b z)).subschemeι n)) :=
    (congrArg (fun γ : finiteCorrespondences (𝟙 (Spec (.of L))) g' => γ.val) hc).trans
      (supportPullbackCycle_val (f := 𝟙 (Spec (.of k))) (g := g)
        (f' := 𝟙 (Spec (.of L))) (g' := g') sq (b z) hy (pointSupport_flat k q (b z)))
  have hs : IsPullback m b' b n :=
    IsPullback.of_vert_isIso ⟨pointAmbientMap_zeroAmbientProjection q⟩
  exact hval.trans (baseChange_closed_support b b' m n hs z).symm

/-- The zero-simplex projection identifies the two scalar pullbacks of a point cycle. -/
theorem zeroProjection_cyclePullback (q : ℕ)
    (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    cyclePullback (k := k) (L := L) 0 q (WeightOne.zeroSimplexProjection k ≫ α) =
      WeightOne.zeroSimplexProjection L ≫ pointCycleFieldChange (k := k) (L := L) q α := by
  let e := (Cor.graphFunctor L).mapIso (zeroSourceIso L)
  apply (cancel_epi e.inv).mp
  change zeroCycleToPoint L q (cyclePullback (k := k) (L := L) 0 q
    (WeightOne.zeroSimplexProjection k ≫ α)) =
      zeroCycleToPoint L q (WeightOne.zeroSimplexProjection L ≫
        pointCycleFieldChange (k := k) (L := L) q α)
  rw [zeroCycleToPoint_precomp]
  have h := DFunLike.congr_fun (pointCycleFieldChange_zeroCycleToPoint (k := k) (L := L) q)
    (WeightOne.zeroSimplexProjection k ≫ α)
  change pointCycleFieldChange (k := k) (L := L) q
      (zeroCycleToPoint k q (WeightOne.zeroSimplexProjection k ≫ α)) =
    zeroCycleToPoint L q (cyclePullback (k := k) (L := L) 0 q
      (WeightOne.zeroSimplexProjection k ≫ α)) at h
  rw [zeroCycleToPoint_precomp] at h
  exact h.symm

/-- The signed pullback in the coefficient universe of the evaluated torus. -/
def liftedCyclePullback (r : Fin 2) (q : ℕ) :
    sections (torusRepresentable k q) (Cor.mk (source k r)) ⟶
      sections (torusRepresentable L q) (Cor.mk (source L r)) :=
  AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up (cyclePullback (k := k) (L := L) r q α.down)
      map_zero' := congrArg ULift.up (map_zero (cyclePullback (k := k) (L := L) r q))
      map_add' := fun α β => congrArg ULift.up
        (map_add (cyclePullback (k := k) (L := L) r q) α.down β.down) }

/-- The lifted scalar restriction preserves the original identity-axis relations. -/
theorem liftedCyclePullback_relations (r : Fin 2) (q : ℕ) :
    (torusRelation k q).app (op (Cor.mk (source k r))) ≫
      liftedCyclePullback (k := k) (L := L) r q ≫
        (toReducedTorus L q).hom.app (op (Cor.mk (source L r))) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change (toReducedTorus L q).hom.app _
    (liftedCyclePullback (k := k) (L := L) r q ((torusRelation k q).app _ s)) = 0
  rw [torusRelation_app_apply, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    let : HasBiproduct (fun _ : Fin (q + 1) => (torusRepresentable k q).obj) :=
      torus_hasBiproduct k (q + 1)
    let X : Cor k := Cor.mk (source k r)
    let Y : Cor L := Cor.mk (source L r)
    let β : X ⟶ Cor.mk (target k q) :=
      ((biproduct.π (fun _ : Fin (q + 1) => (torusRepresentable k q).obj) i).app (op X) s).down
    change (toReducedTorus L (q + 1)).hom.app (op Y)
      (liftedCyclePullback (k := k) (L := L) r (q + 1)
        ((torusIdentityAxis k (q + 1) i).hom.app (op X) (ULift.up β))) = 0
    rw [torusIdentityAxis_app_apply k q i X β]
    change (toReducedTorus L (q + 1)).hom.app (op Y)
      (ULift.up (cyclePullback (k := k) (L := L) r (q + 1)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) q i)))) = 0
    rw [cyclePullback_axis]
    let γ : Y ⟶ Cor.mk (target L q) := cyclePullback (k := k) (L := L) r q β
    have hzero := congrArg (fun f => f.hom.app (op Y))
      (torusIdentityAxis_toReducedTorus L (q + 1) i)
    have hγ := ConcreteCategory.congr_hom hzero (ULift.up γ)
    change (toReducedTorus L (q + 1)).hom.app (op Y)
      ((torusIdentityAxis L (q + 1) i).hom.app (op Y) (ULift.up γ)) = 0 at hγ
    rw [torusIdentityAxis_app_apply L q i Y γ] at hγ
    exact hγ

/-- Field restriction on the original evaluated reduced-torus cokernel. -/
def reducedPullback (r : Fin 2) (q : ℕ) :
    sections (reducedTorus k q) (Cor.mk (source k r)) ⟶
      sections (reducedTorus L q) (Cor.mk (source L r)) :=
  (PreservesCokernel.iso ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj
      (op (Cor.mk (source k r)))) (torusRelation k q)).hom ≫
    cokernel.desc ((torusRelation k q).app (op (Cor.mk (source k r))))
      (liftedCyclePullback (k := k) (L := L) r q ≫
        (toReducedTorus L q).hom.app (op (Cor.mk (source L r))))
      (liftedCyclePullback_relations r q)

@[reassoc]
private theorem toReducedTorus_reducedPullback (r : Fin 2) (q : ℕ) :
    (toReducedTorus k q).hom.app (op (Cor.mk (source k r))) ≫
      reducedPullback (k := k) (L := L) r q =
      liftedCyclePullback (k := k) (L := L) r q ≫
        (toReducedTorus L q).hom.app (op (Cor.mk (source L r))) := by
  change ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk (source k r)))).map
      (cokernel.π (torusRelation k q)) ≫
    ((PreservesCokernel.iso ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj
      (op (Cor.mk (source k r)))) (torusRelation k q)).hom ≫ _) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- Field restriction sends each reduced representative to its actual scalar pullback. -/
@[simp]
theorem reducedPullback_quotient (r : Fin 2) (q : ℕ)
    (α : Cor.mk (source k r) ⟶ Cor.mk (target k q)) :
    reducedPullback (k := k) (L := L) r q
      ((toReducedTorus k q).hom.app (op (Cor.mk (source k r))) (ULift.up α)) =
      (toReducedTorus L q).hom.app (op (Cor.mk (source L r)))
        (ULift.up (cyclePullback (k := k) (L := L) r q α)) :=
  ConcreteCategory.congr_hom (toReducedTorus_reducedPullback r q) (ULift.up α)

/-- Scalar restriction of a rational graph is the graph of the tuple of image units. -/
theorem pointCycleFieldChange_graph (q : ℕ) (a : Fin q → kˣ) :
    pointCycleFieldChange (k := k) (L := L) q ((Cor.graphFunctor k).map (rationalTuple k q a)) =
      (Cor.graphFunctor L).map
        (rationalTuple L q (fun i => Units.map (algebraMap k L).toMonoidHom (a i))) := by
  let f := rationalTuple k q a
  let f' := rationalTuple L q (fun i => Units.map (algebraMap k L).toMonoidHom (a i))
  let X := SmoothSite.base (Spec (.of L))
  let T := target L q
  let j : Spec (.of L) ⟶ pointAmbient L q :=
    correspondenceGraphMap X.hom T.hom f'.left (MorphismProperty.Over.w f')
  let u := pullback.fst (scalarMap (k := k) (E := k)) (scalarMap (k := k) (E := L))
  let v := pullback.snd (scalarMap (k := k) (E := k)) (scalarMap (k := k) (E := L))
  have hscalar : scalarMap (k := k) (E := k) = 𝟙 _ := Spec.map_id _
  let : IsIso v := by
    change IsIso (pullback.snd (scalarMap (k := k) (E := k)) (scalarMap (k := k) (E := L)))
    rw [hscalar]
    infer_instance
  have hu : u ≫ scalarMap (k := k) (E := k) = u :=
    (congrArg (u ≫ ·) hscalar).trans (Category.comp_id _)
  have hv : u = v ≫ scalarMap (k := k) (E := L) := hu.symm.trans pullback.condition
  have hjf : j ≫ pointAmbientStructure L q = 𝟙 (Spec (.of L)) :=
    correspondenceGraphMap_fst X.hom T.hom f'.left (MorphismProperty.Over.w f')
  have hjs : j ≫ pullback.snd X.hom T.hom = f'.left :=
    correspondenceGraphMap_snd X.hom T.hom f'.left (MorphismProperty.Over.w f')
  have hf : f.left ≫ torusMap (k := k) (E := k) q = f.left :=
    (congrArg (f.left ≫ ·) (torusMap_id k q)).trans (Category.comp_id _)
  have hmap : changedPointMap (k := k) (L := L) q f = v ≫ j := by
    apply (pointAmbientMap_isPullback (k := k) (L := L) q).hom_ext
    · rw [changedPointMap_original]
      apply pullback.hom_ext
      · simp only [Category.assoc, finitePointMap_fst, pointAmbientMap_fst]
        change u ≫ scalarMap (k := k) (E := k) =
          v ≫ j ≫ pointAmbientStructure L q ≫ scalarMap (k := k) (E := L)
        rw [← Category.assoc j, hjf]
        exact hu.trans (hv.trans (congrArg (v ≫ ·) (Category.id_comp _).symm))
      · simp only [Category.assoc, finitePointMap_snd, hf, pointAmbientMap_snd]
        change u ≫ f.left = v ≫ j ≫ pullback.snd X.hom T.hom ≫ torusMap (k := k) (E := L) q
        rw [← Category.assoc j, hjs]
        have htuple : f'.left ≫ torusMap (k := k) (E := L) q =
            scalarMap (k := k) (E := L) ≫ f.left := rationalTuple_scalar q a
        rw [htuple, ← Category.assoc v, ← hv]
    · rw [changedPointMap_base, Category.assoc, hjf]
      exact (Category.comp_id v).symm
  apply Subtype.ext
  have hc := pointPushforward_graph_fieldChange_val (k := k) (L := L) q f
  rw [pointPushforward_id, AddMonoidHom.id_apply] at hc
  let : IsClosedImmersion j := isClosedImmersion_correspondenceGraphMap X.hom T.hom
    f'.left (MorphismProperty.Over.w f')
  let : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian (Spec (.of L)))
  let : IsReduced ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsReduced (Spec (.of L)))
  let e : changedPointSupport (k := k) (E := k) (L := L) ≅ Spec (.of L) := asIso v
  have hfund : finiteCyclePushforward v
      (AlgebraicCycle.fundamentalCycle (changedPointSupport (k := k) (E := k) (L := L))) =
      AlgebraicCycle.fundamentalCycle (Spec (.of L)) :=
    finiteCyclePushforward_fundamentalCycle_iso e
  rw [hc, finiteCyclePushforward_congr_hom _ _ hmap, ← finiteCyclePushforward_comp_apply,
    hfund]
  exact finiteCyclePushforward_fundamentalCycle_graph X.hom T.hom f'.left
    (MorphismProperty.Over.w f')

end Algebra

end AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange
