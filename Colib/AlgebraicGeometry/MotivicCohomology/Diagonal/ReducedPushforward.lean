/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FiniteCyclePushforward
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

/-!
# Finite pushforward on reduced diagonal simplex cycles

Finite pushforward carries the graph of each identity-coordinate insertion to
the same axis over the base field. It therefore descends through the actual
evaluated cokernel in every singular degree and weight. The descended map
retains the signed finite-cycle pushforward on represented classes.

Adapted from `Motivic/Cohomology/WeightTwo/Corestriction.lean:206-405` at
`motivic_source_a6805c4`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalReducedPushforward

open _root_.AlgebraicGeometry.Scheme SmoothSite
open DiagonalFiniteCyclePushforward PresheafWithTransfers

/-- Maps to the underlying torus power agree when their base and coordinates agree. -/
theorem torusPower_left_hom_ext {S W : Scheme.{u}} (q : ℕ)
    {f g : W ⟶ (torusPower S q).left}
    (hbase : f ≫ (torusPower S q).hom = g ≫ (torusPower S q).hom)
    (hcoords : ∀ i : Fin q, f ≫ (torusCoordinate S q i).left =
      g ≫ (torusCoordinate S q i).left) : f = g := by
  induction q with
  | zero =>
    let f₀ : W ⟶ S := f
    let g₀ : W ⟶ S := g
    have h : f₀ ≫ 𝟙 S = g₀ ≫ 𝟙 S := hbase
    exact (Category.comp_id f₀).symm.trans (h.trans (Category.comp_id g₀))
  | succ q ih =>
    apply pullback.hom_ext
    · exact hcoords 0
    · apply ih
      · have h := MorphismProperty.Over.w
          (productSnd (multiplicativeGroupObject S) (torusPower S q))
        change pullback.snd _ _ ≫ (torusPower S q).hom = (torusPower S (q + 1)).hom at h
        simpa only [Category.assoc, h] using hbase
      · intro i
        simpa only [torusCoordinate_succ, MorphismProperty.Comma.comp_left, productSnd,
          homMk_left, Category.assoc] using hcoords i.succ

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- Scalar projection commutes with each of the original Laurent coordinates. -/
@[reassoc]
theorem torusMap_coordinate (q : ℕ) (i : Fin q) :
    torusMap (k := k) (E := E) q ≫ (torusCoordinate (Spec (.of k)) q i).left =
      (torusCoordinate (Spec (.of E)) q i).left ≫ multiplicativeGroupMap (k := k) (E := E) := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact pullback.lift_fst _ _ _
    · have h : torusMap (k := k) (E := E) (q + 1) ≫
            pullback.snd (multiplicativeGroupObject (Spec (.of k))).hom (target k q).hom =
          pullback.snd (multiplicativeGroupObject (Spec (.of E))).hom (target E q).hom ≫
            torusMap (k := k) (E := E) q := pullback.lift_snd _ _ _
      simp only [torusCoordinate_succ, MorphismProperty.Comma.comp_left, productSnd, homMk_left]
      rw [← Category.assoc, h, Category.assoc, ih j, Category.assoc]

private theorem torusOne_left_fst (S : Scheme.{u}) :
    (torusOne S).left ≫ pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S) =
    (unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := S)).symm
      (1 : (Γ(S, ⊤))ˣ) := by
  let e := unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := S)
  let one : (Γ(S, ⊤))ˣ := 1
  apply e.injective
  have h : e ((torusOne S).left ≫
      pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S)) = one := torusOneOver_represents_one S
  exact h.trans (e.apply_symm_apply one).symm

private theorem comp_absolute_unit_one {S T : Scheme.{u}} (f : T ⟶ S) :
    f ≫ (unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := S)).symm
      (1 : (Γ(S, ⊤))ˣ) =
    (unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := T)).symm
      (1 : (Γ(T, ⊤))ˣ) := by
  let e := unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := T)
  have h : Units.map f.appTop.hom.toMonoidHom (1 : (Γ(S, ⊤))ˣ) = (1 : (Γ(T, ⊤))ˣ) :=
    map_one _
  exact (unitsOfGlobalSectionsCanonicalRepresentation.comp_homEquiv_symm
    (X := T) (X' := S) (1 : (Γ(S, ⊤))ˣ) f).trans (congrArg e.symm h)

/-- The scalar map of the multiplicative groups preserves the actual unit sections. -/
theorem multiplicativeGroupMap_one :
    (torusOne (Spec (.of E))).left ≫ multiplicativeGroupMap (k := k) (E := E) =
      scalarMap (k := k) (E := E) ≫ (torusOne (Spec (.of k))).left := by
  let p := multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ))
  let b := specULiftZIsTerminal.from (Spec (.of k))
  let b' := specULiftZIsTerminal.from (Spec (.of E))
  apply pullback.hom_ext (f := p) (g := b)
  · have h : multiplicativeGroupMap (k := k) (E := E) ≫ pullback.fst p b =
        pullback.fst p b' := pullback.lift_fst _ _ _
    have hE : (torusOne (Spec (.of E))).left ≫ pullback.fst p b' =
        (unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := Spec (.of E))).symm
          (1 : (Γ(Spec (.of E), ⊤))ˣ) := torusOne_left_fst (Spec (.of E))
    have hk : (torusOne (Spec (.of k))).left ≫ pullback.fst p b =
        (unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := Spec (.of k))).symm
          (1 : (Γ(Spec (.of k), ⊤))ˣ) := torusOne_left_fst (Spec (.of k))
    rw [Category.assoc, Category.assoc, h, hE, hk]
    exact (comp_absolute_unit_one (scalarMap (k := k) (E := E))).symm
  · have h := (multiplicativeGroupMap_isPullback (k := k) (E := E)).w
    change multiplicativeGroupMap (k := k) (E := E) ≫ pullback.snd p b =
      pullback.snd p b' ≫ scalarMap (k := k) (E := E) at h
    have hE := MorphismProperty.Over.w (torusOne (Spec (.of E)))
    have hk := MorphismProperty.Over.w (torusOne (Spec (.of k)))
    change (torusOne (Spec (.of E))).left ≫ pullback.snd p b' = 𝟙 (Spec (.of E)) at hE
    change (torusOne (Spec (.of k))).left ≫ pullback.snd p b = 𝟙 (Spec (.of k)) at hk
    rw [Category.assoc, Category.assoc, h, ← Category.assoc, hE, hk]
    exact (Category.id_comp (scalarMap (k := k) (E := E))).trans
      (Category.comp_id (scalarMap (k := k) (E := E))).symm

/-- Scalar projection commutes with the literal identity-coordinate insertion. -/
@[reassoc]
theorem torusMap_insertOne (q : ℕ) (i : Fin (q + 1)) :
    (torusInsertOne (Spec (.of E)) q i).left ≫ torusMap (k := k) (E := E) (q + 1) =
      torusMap (k := k) (E := E) q ≫ (torusInsertOne (Spec (.of k)) q i).left := by
  apply torusPower_left_hom_ext (q + 1)
  · calc
      _ = (target E q).hom ≫ scalarMap (k := k) (E := E) := by
        rw [Category.assoc, (torusMap_isPullback (k := k) (E := E) (q + 1)).w,
          ← Category.assoc, MorphismProperty.Over.w (torusInsertOne (Spec (.of E)) q i)]
      _ = _ := by
        rw [Category.assoc, MorphismProperty.Over.w (torusInsertOne (Spec (.of k)) q i),
          (torusMap_isPullback (k := k) (E := E) q).w]
  · intro j
    rw [Category.assoc, Category.assoc, torusMap_coordinate, ← Category.assoc]
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
    · rw [torusInsertOne_left_coordinate_self, torusInsertOne_left_coordinate_self,
        Category.assoc, multiplicativeGroupMap_one,
        ← Category.assoc (torusMap (k := k) (E := E) q),
        (torusMap_isPullback (k := k) (E := E) q).w, Category.assoc]
    · rw [torusInsertOne_left_coordinate_succAbove, torusInsertOne_left_coordinate_succAbove,
        torusMap_coordinate]

/-- The original identity-axis insertion on the simplex-times-torus ambient. -/
abbrev axisMap (F : Type u) [Field F] (r q : ℕ) (i : Fin (q + 1)) :
    ambient F r q ⟶ ambient F r (q + 1) :=
  Cor.graphTargetMap F (source F r) (torusInsertOne (Spec (.of F)) q i)

/-- The coefficient projection commutes with each original axis map. -/
theorem ambientMap_axis (r q : ℕ) (i : Fin (q + 1)) :
    axisMap E r q i ≫ ambientMap (k := k) (E := E) r (q + 1) =
      ambientMap (k := k) (E := E) r q ≫ axisMap k r q i := by
  apply pullback.hom_ext
  · simp only [axisMap, Category.assoc, ambientMap_fst,
      Cor.graphTargetMap_fst, Cor.graphTargetMap_fst_assoc]
  · simp only [axisMap, Category.assoc, ambientMap_snd, ambientMap_snd_assoc,
      Cor.graphTargetMap_snd, Cor.graphTargetMap_snd_assoc, torusMap_insertOne]

variable [Module.Finite k E]

/-- Every signed cycle through an identity axis transfers to that same axis. -/
theorem cyclePushforward_axis (r q : ℕ) (i : Fin (q + 1))
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E q)) :
    cyclePushforward (k := k) (E := E) r (q + 1)
      (α ≫ (Cor.graphFunctor E).map (torusInsertOne (Spec (.of E)) q i)) =
    cyclePushforward (k := k) (E := E) r q α ≫
      (Cor.graphFunctor k).map (torusInsertOne (Spec (.of k)) q i) := by
  apply Subtype.ext
  rw [cyclePushforward_val,
    Cor.comp_graph_val_of_finite E (torusInsertOne (Spec (.of E)) q i) α,
    Cor.comp_graph_val_of_finite k (torusInsertOne (Spec (.of k)) q i)
      (cyclePushforward (k := k) (E := E) r q α),
    cyclePushforward_val, finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply]
  have h (f g : ambient E r q ⟶ ambient k r (q + 1))
      [IsFinite f] [IsFinite g] (e : f = g) :
      finiteCyclePushforward f α.val = finiteCyclePushforward g α.val := by
    cases e
    rfl
  exact h _ _ (ambientMap_axis r q i)

/-- The original signed-cycle pushforward in the coefficient universe of the reduced torus. -/
def liftedCyclePushforward (r q : ℕ) :
    sections (torusRepresentable E q) (Cor.mk (source E r)) ⟶
      sections (torusRepresentable k q) (Cor.mk (source k r)) :=
  AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up (cyclePushforward (k := k) (E := E) r q α.down)
      map_zero' := congrArg ULift.up (map_zero (cyclePushforward (k := k) (E := E) r q))
      map_add' := fun α β => congrArg ULift.up
        (map_add (cyclePushforward (k := k) (E := E) r q) α.down β.down) }

/-- Pushforward followed by the target quotient kills the original source relation map. -/
theorem liftedCyclePushforward_relations (r q : ℕ) :
    (torusRelation E q).app (op (Cor.mk (source E r))) ≫
      liftedCyclePushforward (k := k) (E := E) r q ≫
        (toReducedTorus k q).hom.app (op (Cor.mk (source k r))) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change (toReducedTorus k q).hom.app _
    (liftedCyclePushforward (k := k) (E := E) r q
      ((torusRelation E q).app _ s)) = 0
  rw [torusRelation_app_apply, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    let : HasBiproduct (fun _ : Fin (q + 1) => (torusRepresentable E q).obj) :=
      torus_hasBiproduct E (q + 1)
    let X : Cor E := Cor.mk (source E r)
    let Y : Cor k := Cor.mk (source k r)
    let β : X ⟶ Cor.mk (target E q) :=
      ((biproduct.π (fun _ : Fin (q + 1) => (torusRepresentable E q).obj) i).app (op X) s).down
    change (toReducedTorus k (q + 1)).hom.app (op Y)
      (liftedCyclePushforward (k := k) (E := E) r (q + 1)
        ((torusIdentityAxis E (q + 1) i).hom.app (op X) (ULift.up β))) = 0
    rw [torusIdentityAxis_app_apply E q i X β]
    have h := cyclePushforward_axis (k := k) (E := E) r q i β
    let γ : Y ⟶ Cor.mk (target k (q + 1)) :=
      cyclePushforward (k := k) (E := E) r (q + 1)
        (β ≫ (Cor.graphFunctor E).map (torusInsertOne (Spec (.of E)) q i))
    change (toReducedTorus k (q + 1)).hom.app (op Y) (ULift.up γ) = 0
    dsimp only [γ]
    rw [h]
    let η : Y ⟶ Cor.mk (target k q) := cyclePushforward (k := k) (E := E) r q β
    have hzero := congrArg (fun f => f.hom.app (op Y))
      (torusIdentityAxis_toReducedTorus k (q + 1) i)
    have hη := ConcreteCategory.congr_hom hzero (ULift.up η)
    change (toReducedTorus k (q + 1)).hom.app (op Y)
      ((torusIdentityAxis k (q + 1) i).hom.app (op Y) (ULift.up η)) = 0 at hη
    rw [torusIdentityAxis_app_apply k q i Y η] at hη
    exact hη

/-- Finite pushforward on the actual evaluated reduced-torus cokernels. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightTwo/Corestriction.lean:387-405"
  "adaptation" "Degreewise transfer through the original identity-axis quotient"]
def reducedPushforward (r q : ℕ) :
    sections (reducedTorus E q) (Cor.mk (source E r)) ⟶
      sections (reducedTorus k q) (Cor.mk (source k r)) :=
  (PreservesCokernel.iso ((evaluation (Cor E)ᵒᵖ AddCommGrpCat).obj
      (op (Cor.mk (source E r)))) (torusRelation E q)).hom ≫
    cokernel.desc ((torusRelation E q).app (op (Cor.mk (source E r))))
      (liftedCyclePushforward (k := k) (E := E) r q ≫
        (toReducedTorus k q).hom.app (op (Cor.mk (source k r))))
      (liftedCyclePushforward_relations r q)

/-- The descent keeps the actual signed-cycle map on the quotient representatives. -/
@[reassoc]
theorem toReducedTorus_reducedPushforward (r q : ℕ) :
    (toReducedTorus E q).hom.app (op (Cor.mk (source E r))) ≫
      reducedPushforward (k := k) (E := E) r q =
    liftedCyclePushforward (k := k) (E := E) r q ≫
      (toReducedTorus k q).hom.app (op (Cor.mk (source k r))) := by
  change ((evaluation (Cor E)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk (source E r)))).map
      (cokernel.π (torusRelation E q)) ≫
    ((PreservesCokernel.iso ((evaluation (Cor E)ᵒᵖ AddCommGrpCat).obj
      (op (Cor.mk (source E r)))) (torusRelation E q)).hom ≫ _) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- The descended map sends a represented section to the class of its finite pushforward. -/
@[simp]
theorem reducedPushforward_quotient (r q : ℕ)
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E q)) :
    reducedPushforward (k := k) (E := E) r q
      ((toReducedTorus E q).hom.app (op (Cor.mk (source E r))) (ULift.up α)) =
    (toReducedTorus k q).hom.app (op (Cor.mk (source k r)))
      (ULift.up (cyclePushforward (k := k) (E := E) r q α)) :=
  ConcreteCategory.congr_hom (toReducedTorus_reducedPushforward r q) (ULift.up α)

end AlgebraicGeometry.MotivicCohomology.DiagonalReducedPushforward
