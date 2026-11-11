/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.GroupScheme.UnitPoints
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PointNorm

/-!
# Milnor evaluation on the reduced torus at the field point

The native pushforward along an identity axis is supported on that axis.
The inserted coordinate is one on each integral support, so the norm
annihilates the defining relation map of the reduced transfer presheaf.

Adapted from `motivic_source_a6805c4`, using the native graph pushforward
and the existing coordinate units on the integral components.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalReducedPointNorm

open _root_.AlgebraicGeometry.Scheme
open SmoothSite PresheafWithTransfers DiagonalTopDegree DiagonalCycleSymbols DiagonalPointNorm

variable (k : Type u) [Field k]

private abbrev axisAmbientMap (q : ℕ) (i : Fin (q + 1)) :=
  Cor.graphTargetMap k (base (Spec (.of k))) (torusInsertOne (Spec (.of k)) q i)

private theorem coordinateUnit_axis (q : ℕ) (i : Fin (q + 1))
    (x : (pullback (C := Scheme) (𝟙 (Spec (.of k))) (torusPower (Spec (.of k)) q).hom :
      Scheme.{u}))
    (hx : IsFiniteCorrespondencePoint (𝟙 (Spec (.of k)))
      (torusPower (Spec (.of k)) (q + 1)).hom ((axisAmbientMap k q i).base x)) :
    coordinateUnit (⟨(axisAmbientMap k q i).base x, hx⟩ : Generator k (q + 1)) i = 1 := by
  let S := Spec (.of k)
  let j := axisAmbientMap k q i
  let Z : Generator k (q + 1) := ⟨j.base x, hx⟩
  have hbase : pullback.snd (𝟙 S) (torusPower S q).hom ≫ (torusPower S q).hom =
      pullback.fst (𝟙 S) (torusPower S q).hom := by
    simpa only [Category.comp_id] using
      (pullback.condition (f := 𝟙 S) (g := (torusPower S q).hom)).symm
  have hj : j ≫ pullback.snd (𝟙 S) (torusPower S (q + 1)).hom ≫
      (torusCoordinate S (q + 1) i).left =
      j ≫ pullback.fst (𝟙 S) (torusPower S (q + 1)).hom ≫ (torusOne S).left := by
    change Cor.graphTargetMap k (base S) (torusInsertOne S q i) ≫
        pullback.snd (base S).hom (torusPower S (q + 1)).hom ≫
          (torusCoordinate S (q + 1) i).left =
      Cor.graphTargetMap k (base S) (torusInsertOne S q i) ≫
        pullback.fst (base S).hom (torusPower S (q + 1)).hom ≫ (torusOne S).left
    rw [Cor.graphTargetMap_snd_assoc, Cor.graphTargetMap_fst_assoc,
      torusInsertOne_left_coordinate_self,
      ← Category.assoc (pullback.snd (base S).hom (torusPower S q).hom)]
    exact congrArg (fun f => f ≫ (torusOne S).left) hbase
  let : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (axisAmbientMap k q i))
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt_comp j x
  have hcoord : targetProjection Z ≫ (torusCoordinate S (q + 1) i).left =
      projection Z ≫ (torusOne S).left := by
    apply (cancel_epi e.hom).mp
    simpa only [targetProjection, projection, Z, ← Category.assoc, he] using
      congrArg (fun f => (integralComponentAt x).subschemeι ≫ f) hj
  have hone :
      Units.map (torusOne S).left.appTop.hom.toMonoidHom
        (multiplicativeGroupBaseChangeCoordinate S) = (1 : (Γ(S, ⊤))ˣ) :=
    nativeTorusPoint_coordinate (𝟙 S) 1
  change coordinateUnit Z i = 1
  apply Units.ext
  change (targetProjection Z ≫ (torusCoordinate S (q + 1) i).left).appTop.hom
    (multiplicativeGroupBaseChangeCoordinate S).val = 1
  rw [hcoord, Scheme.Hom.comp_appTop]
  change (projection Z).appTop.hom
    ((torusOne S).left.appTop.hom (multiplicativeGroupBaseChangeCoordinate S).val) = 1
  rw [show (torusOne S).left.appTop.hom
    (multiplicativeGroupBaseChangeCoordinate S).val = 1 from congrArg Units.val hone, map_one]

/-- Every signed point correspondence through an identity axis has zero Milnor evaluation. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/FinitePointEvaluation.lean:318-370"
  "adaptation" "Native pushforward support and the inserted unit coordinate"]
theorem cycleValue_axis (q : ℕ) (i : Fin (q + 1)) (α : point k ⟶ target k q) :
    cycleValue k (q + 1) (α ≫ (Cor.graphFunctor k).map
      (torusInsertOne (Spec (.of k)) q i)) = 0 := by
  let j := axisAmbientMap k q i
  let : IsFinite j := inferInstanceAs (IsFinite (axisAmbientMap k q i))
  apply cycleValue_eq_zero_of_identity_support
  rintro ⟨z, hz⟩ hn
  have hs : z ∈ (finiteCyclePushforward j α.val).support := by
    rw [← Cor.comp_graph_val_of_finite k (torusInsertOne (Spec (.of k)) q i) α]
    exact hn
  obtain ⟨x, _, rfl⟩ := finiteCyclePushforward_support_subset j α.val hs
  exact ⟨i, coordinateUnit_axis k q i x hz⟩

/-- The signed point norm in the coefficient universe of the reduced transfer presheaf. -/
def largeCycleNorm (q : ℕ) : sections (torusRepresentable k q) (point k) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (MilnorKTheory k q)) :=
  AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up (cycleValue k q α.down)
      map_zero' := congrArg ULift.up (map_zero (cycleValue k q))
      map_add' := fun α β => congrArg ULift.up (map_add (cycleValue k q) α.down β.down) }

/-- The original identity-axis relation morphism is killed by the point norm. -/
theorem relation_largeCycleNorm (q : ℕ) :
    (torusRelation k q).app (op (point k)) ≫ largeCycleNorm k q = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change largeCycleNorm k q ((torusRelation k q).app (op (point k)) s) = 0
  rw [torusRelation_app_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    let : HasBiproduct (fun _ : Fin (q + 1) => (torusRepresentable k q).obj) :=
      torus_hasBiproduct k (q + 1)
    let β : point k ⟶ target k q :=
      ((biproduct.π (fun _ : Fin (q + 1) => (torusRepresentable k q).obj) i).app
        (op (point k)) s).down
    change largeCycleNorm k (q + 1)
      ((torusIdentityAxis k (q + 1) i).hom.app (op (point k)) (ULift.up β)) = 0
    rw [torusIdentityAxis_app_apply k q i (point k) β]
    exact congrArg ULift.up (cycleValue_axis k q i β)

/-- Point norm through the actual evaluated reduced-torus cokernel. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/ReducedPointNorm.lean:25-85"
  "adaptation" "Signed native point evaluation on the actual reduced-transfer quotient"]
def reducedNormLarge (q : ℕ) : sections (reducedTorus k q) (point k) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (MilnorKTheory k q)) :=
  (PreservesCokernel.iso
      ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (point k))) (torusRelation k q)).hom ≫
    cokernel.desc ((torusRelation k q).app (op (point k)))
      (largeCycleNorm k q) (relation_largeCycleNorm k q)

/-- The descended norm extends the original signed evaluation along the literal quotient. -/
@[reassoc]
theorem toReducedTorus_reducedNormLarge (q : ℕ) :
    (toReducedTorus k q).hom.app (op (point k)) ≫ reducedNormLarge k q = largeCycleNorm k q := by
  change ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (point k))).map
    (cokernel.π (torusRelation k q)) ≫ _ = _
  rw [reducedNormLarge, PreservesCokernel.π_iso_hom_assoc]
  exact cokernel.π_desc _ _ _

/-- The reduced norm valued in the native homogeneous Milnor group. -/
def reducedNorm (q : ℕ) : sections (reducedTorus k q) (point k) →+ MilnorKTheory k q where
  toFun s := (reducedNormLarge k q s).down
  map_zero' := congrArg ULift.down (map_zero (reducedNormLarge k q).hom)
  map_add' s t := congrArg ULift.down (map_add (reducedNormLarge k q).hom s t)

/-- On a represented reduced section, the norm is the original signed point norm. -/
@[simp] theorem reducedNorm_quotient (q : ℕ) (α : point k ⟶ target k q) :
    reducedNorm k q ((toReducedTorus k q).hom.app (op (point k)) (ULift.up α)) =
      cycleValue k q α :=
  congrArg ULift.down
    (ConcreteCategory.congr_hom (toReducedTorus_reducedNormLarge k q) (ULift.up α))

end AlgebraicGeometry.MotivicCohomology.DiagonalReducedPointNorm
