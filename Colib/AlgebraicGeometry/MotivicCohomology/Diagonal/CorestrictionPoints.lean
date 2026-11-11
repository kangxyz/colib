/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.Corestriction
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols
public import Colib.AlgebraicGeometry.Chow.IntegralFundamental

/-!
# Finite corestriction of diagonal point cycles

The actual zero-simplex projection identifies the finite transfer of point
representatives with native finite pushforward. In particular, a rational
graph transfers as the full fundamental cycle of its finite field point.

Adapted from `Motivic/Cohomology/Diagonal/Corestriction.lean:113-245` at
`motivic_source_a6805c4`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow
open Function.locallyFinsuppWithin

universe u w

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

open _root_.AlgebraicGeometry.Scheme
open DiagonalTopDegree DiagonalFiniteCyclePushforward DiagonalReducedPushforward
open DiagonalCycleSymbols (cycleClass cycleClass_apply graphSymbol rationalTuple)
open PresheafWithTransfers

/-- The native point-times-torus ambient scheme. -/
abbrev pointAmbient (F : Type u) [Field F] (q : ℕ) : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of F))).hom (target F q).hom

/-- The actual projection removing the zero simplex. -/
abbrev zeroProjection (F : Type u) [Field F] :
    source F 0 ⟶ SmoothSite.base (Spec (.of F)) :=
  SmoothSite.productFst _ _

instance zeroProjection_isIso (F : Type u) [Field F] :
    IsIso (zeroProjection F).left := by
  have h : (simplexChart0 F).hom = AlgebraicSimplex.structureMap F 0 := by
    change Spec.map (CommRingCat.ofHom (zeroCoordinateEquiv F).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgebraicSimplex.constant F 0))
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (zeroCoordinateEquiv F).symm.commutes
  change IsIso (pullback.fst (𝟙 (Spec (.of F))) (AlgebraicSimplex.structureMap F 0))
  rw [← h]
  infer_instance

/-- The actual zero-simplex projection is a smooth-site isomorphism. -/
def zeroSourceIso (F : Type u) [Field F] :
    source F 0 ≅ SmoothSite.base (Spec (.of F)) where
  hom := zeroProjection F
  inv := SmoothSite.homMk (inv (zeroProjection F).left) (by
    rw [← MorphismProperty.Over.w (zeroProjection F), IsIso.inv_hom_id_assoc])
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact IsIso.hom_inv_id _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact IsIso.inv_hom_id _

/-- Forgetting the zero simplex on the native correspondence ambient. -/
abbrev zeroAmbientProjection (F : Type u) [Field F] (q : ℕ) :
    ambient F 0 q ⟶ pointAmbient F q :=
  correspondenceGraphFiberAmbientMap (source F 0).hom
    (SmoothSite.base (Spec (.of F))).hom (target F q).hom
    (zeroProjection F).left (MorphismProperty.Over.w (zeroProjection F))

instance zeroAmbientProjection_isIso (F : Type u) [Field F] (q : ℕ) :
    IsIso (zeroAmbientProjection F q) := by
  unfold zeroAmbientProjection correspondenceGraphFiberAmbientMap
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

@[reassoc] private theorem zeroAmbientProjection_fst (F : Type u) [Field F] (q : ℕ) :
    zeroAmbientProjection F q ≫
      pullback.fst (SmoothSite.base (Spec (.of F))).hom (target F q).hom =
    pullback.fst (source F 0).hom (target F q).hom ≫ (zeroProjection F).left :=
  pullback.lift_fst _ _ _

@[reassoc] private theorem zeroAmbientProjection_snd (F : Type u) [Field F] (q : ℕ) :
    zeroAmbientProjection F q ≫
      pullback.snd (SmoothSite.base (Spec (.of F))).hom (target F q).hom =
    pullback.snd (source F 0).hom (target F q).hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- Equality of scheme maps gives equality of their finite cycle pushforwards. -/
theorem finiteCyclePushforward_congr_map {X Y : Scheme.{u}}
    (m n : X ⟶ Y) [IsFinite m] [IsFinite n] (h : m = n) (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward m c = finiteCyclePushforward n c := by
  cases h
  rfl

open Classical in
private theorem zeroProjection_prime (F : Type u) [Field F] (q : ℕ)
    (z : pointAmbient F q)
    (hz : IsFiniteCorrespondencePoint (SmoothSite.base (Spec (.of F))).hom (target F q).hom z) :
    finiteCyclePushforward (zeroAmbientProjection F q)
      ((WeightOne.zeroSimplexProjection F ≫
        singleFiniteCorrespondence (SmoothSite.base (Spec (.of F))).hom (target F q).hom
          z hz 1).val) = single z 1 := by
  let X := source F 0
  let Y := SmoothSite.base (Spec (.of F))
  let T := target F q
  let π := (integralComponentAt z).subschemeι ≫ pullback.fst Y.hom T.hom
  let : IsFinite π := hz.1
  let : IsNoetherian X.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of F)) X.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of F)) X.hom }
  let : IsNoetherian (integralComponentAt z).subscheme :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) π
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (Y := Y.left) π }
  let : Subsingleton (Spec (.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let : Flat π := Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of F)) _
  let j := correspondenceGraphFiberMap X.hom Y.hom T.hom z
    (zeroProjection F).left (MorphismProperty.Over.w (zeroProjection F))
  let : IsFinite j := isFinite_correspondenceGraphFiberMap _ _ _ _ _ _ hz
  let : IsNoetherian (correspondenceGraphFiber Y.hom T.hom z (zeroProjection F).left) :=
    isNoetherian_correspondenceGraphFiber Y.hom T.hom z (zeroProjection F).left hz
  let e : correspondenceGraphFiber Y.hom T.hom z (zeroProjection F).left ≅
      (integralComponentAt z).subscheme := asIso (pullback.snd (zeroProjection F).left π)
  have he : j ≫ zeroAmbientProjection F q = e.hom ≫ (integralComponentAt z).subschemeι := by
    apply pullback.hom_ext
    · simp only [Category.assoc, zeroAmbientProjection_fst]
      change j ≫ pullback.fst X.hom T.hom ≫ (zeroProjection F).left =
        pullback.snd (zeroProjection F).left π ≫ π
      exact (correspondenceGraphFiberMap_fst_assoc X.hom Y.hom T.hom z (zeroProjection F).left
        (MorphismProperty.Over.w (zeroProjection F)) _).trans pullback.condition
    · simp only [Category.assoc, zeroAmbientProjection_snd]
      change j ≫ pullback.snd X.hom T.hom =
        pullback.snd (zeroProjection F).left π ≫
          (integralComponentAt z).subschemeι ≫ pullback.snd Y.hom T.hom
      exact correspondenceGraphFiberMap_snd X.hom Y.hom T.hom z (zeroProjection F).left _
  change finiteCyclePushforward (zeroAmbientProjection F q)
    (((Cor.graphFunctor F).map (zeroProjection F) ≫
      singleFiniteCorrespondence Y.hom T.hom z hz 1).val) = _
  rw [Cor.graph_comp_single_val_eq_fiber (X := X) (Y := Y) (Z := T) F z hz (zeroProjection F)]
  change finiteCyclePushforward (zeroAmbientProjection F q)
    (finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle _)) = _
  rw [finiteCyclePushforward_comp_apply]
  refine (finiteCyclePushforward_congr_map _ _ he _).trans ?_
  rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso]
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  rw [finiteCyclePushforward_fundamentalCycle_integral, subschemeι_genericPoint_integralComponentAt]

/-- Inserting the zero-simplex projection and then forgetting it preserves the signed cycle. -/
theorem zeroProjection_cycle (F : Type u) [Field F] (q : ℕ)
    (α : point F ⟶ DiagonalCycleSymbols.target F q) :
    finiteCyclePushforward (zeroAmbientProjection F q)
      (WeightOne.zeroSimplexProjection F ≫ α).val = α.val := by
  let Y := SmoothSite.base (Spec (.of F))
  let T := target F q
  have h : (finiteCyclePushforward (zeroAmbientProjection F q)).comp
      ((finiteCorrespondences (source F 0).hom T.hom).subtype.comp
        (Preadditive.leftComp (Cor.mk T) (WeightOne.zeroSimplexProjection F))) =
      (finiteCorrespondences Y.hom T.hom).subtype := by
    apply finiteCorrespondences.addHom_ext_one Y.hom T.hom
    intro z hz
    exact zeroProjection_prime F q z hz
  exact DFunLike.congr_fun h α

/-- Signed point cycles represent every raw diagonal class. -/
theorem cycleClass_surjective (F : Type u) [Field F] (q : ℕ) :
    Function.Surjective (cycleClass F q) := by
  intro x
  obtain ⟨y, rfl⟩ := singularClass_surjective F q x
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective F q (Cor.mk (source F 0)) y
  let e := (Cor.graphFunctor F).mapIso (zeroSourceIso F)
  refine ⟨e.inv ≫ α, ?_⟩
  rw [cycleClass_apply]
  change singularClass F q ((toReducedTorus F q).hom.app _ (ULift.up (e.hom ≫ e.inv ≫ α))) =
    singularClass F q ((toReducedTorus F q).hom.app _ (ULift.up α))
  rw [Iso.hom_inv_id_assoc]

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The scalar projection on the point-times-torus ambient scheme. -/
def pointAmbientMap (q : ℕ) : pointAmbient E q ⟶ pointAmbient k q :=
  pullback.map _ _ _ _ (scalarMap (k := k) (E := E)) (torusMap (k := k) (E := E) q)
    (scalarMap (k := k) (E := E)) (by simp [SmoothSite.base]) (torusMap_isPullback q).w.symm

@[reassoc (attr := simp)] theorem pointAmbientMap_fst (q : ℕ) :
    pointAmbientMap (k := k) (E := E) q ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k q).hom =
    pullback.fst (SmoothSite.base (Spec (.of E))).hom (target E q).hom ≫ scalarMap :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pointAmbientMap_snd (q : ℕ) :
    pointAmbientMap (k := k) (E := E) q ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k q).hom =
    pullback.snd (SmoothSite.base (Spec (.of E))).hom (target E q).hom ≫ torusMap (k := k) q :=
  pullback.lift_snd _ _ _

/-- Forgetting the zero simplex commutes with the original scalar projection. -/
theorem pointAmbientMap_zeroAmbientProjection (q : ℕ) :
    ambientMap (k := k) (E := E) 0 q ≫ zeroAmbientProjection k q =
      zeroAmbientProjection E q ≫ pointAmbientMap (k := k) (E := E) q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, zeroAmbientProjection_fst, ambientMap_fst_assoc,
      pointAmbientMap_fst, zeroAmbientProjection_fst_assoc]
    congr 1
    change DiagonalFiniteCyclePushforward.sourceMap (k := k) (E := E) 0 ≫
        pullback.fst (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k 0) =
      pullback.fst (SmoothSite.base (Spec (.of E))).hom (AlgebraicSimplex.structureMap E 0) ≫
        scalarMap
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, zeroAmbientProjection_snd, ambientMap_snd,
      pointAmbientMap_snd, zeroAmbientProjection_snd_assoc]

/-- The finite point obtained from the actual graph and scalar projection. -/
def finitePointMap (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q) :
    Spec (.of E) ⟶ pointAmbient k q :=
  correspondenceGraphMap (SmoothSite.base (Spec (.of E))).hom (target E q).hom
    f.left (MorphismProperty.Over.w f) ≫ pointAmbientMap (k := k) (E := E) q

@[reassoc (attr := simp)] theorem finitePointMap_fst (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q) :
    finitePointMap (k := k) q f ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k q).hom =
    scalarMap (k := k) (E := E) := by
  simp only [finitePointMap, Category.assoc, pointAmbientMap_fst,
    correspondenceGraphMap_fst_assoc]

@[reassoc (attr := simp)] theorem finitePointMap_snd (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q) :
    finitePointMap (k := k) q f ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k q).hom =
    f.left ≫ torusMap (k := k) q := by
  simp only [finitePointMap, Category.assoc, pointAmbientMap_snd, correspondenceGraphMap_snd_assoc]

variable [Module.Finite k E]

private theorem scalarMap_isFinite : IsFinite (scalarMap (k := k) (E := E)) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance pointAmbientMap_isFinite (q : ℕ) : IsFinite (pointAmbientMap (k := k) (E := E) q) := by
  have h := productMap_isPullback (IsPullback.id_vert (scalarMap (k := k) (E := E)))
    (torusMap_isPullback (k := k) (E := E) q)
  exact MorphismProperty.of_isPullback h.flip (scalarMap_isFinite (k := k) (E := E))

instance finitePointMap_isFinite (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q) :
    IsFinite (finitePointMap (k := k) q f) := by
  have := isClosedImmersion_correspondenceGraphMap (SmoothSite.base (Spec (.of E))).hom
    (target E q).hom f.left (MorphismProperty.Over.w f)
  unfold finitePointMap
  infer_instance

/-- The same signed-cycle pushforward with the zero simplex removed. -/
def pointPushforward (q : ℕ) :
    (point E ⟶ DiagonalCycleSymbols.target E q) →+ (point k ⟶ DiagonalCycleSymbols.target k q) :=
  (Preadditive.leftComp (Cor.mk (target k q)) ((Cor.graphFunctor k).map (zeroSourceIso k).inv)).comp
    ((cyclePushforward (k := k) (E := E) 0 q).comp
      (Preadditive.leftComp (Cor.mk (target E q)) (WeightOne.zeroSimplexProjection E)))

private theorem zeroProjection_pointPushforward (q : ℕ)
    (α : point E ⟶ DiagonalCycleSymbols.target E q) :
    WeightOne.zeroSimplexProjection k ≫ pointPushforward (k := k) q α =
      cyclePushforward (k := k) 0 q (WeightOne.zeroSimplexProjection E ≫ α) := by
  let e := (Cor.graphFunctor k).mapIso (zeroSourceIso k)
  change e.hom ≫ e.inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The point transfer preserves the actual finite pushforward, including signed multiplicities. -/
theorem pointPushforward_val (q : ℕ) (α : point E ⟶ DiagonalCycleSymbols.target E q) :
    (pointPushforward (k := k) q α).val =
      finiteCyclePushforward (pointAmbientMap (k := k) q) α.val :=
  calc
    _ = finiteCyclePushforward (zeroAmbientProjection k q)
          ((WeightOne.zeroSimplexProjection k ≫ pointPushforward (k := k) q α).val) :=
      (zeroProjection_cycle k q _).symm
    _ = _ := by
      let a : Cor.mk (source E 0) ⟶ Cor.mk (target E q) :=
        WeightOne.zeroSimplexProjection E ≫ α
      rw [zeroProjection_pointPushforward, cyclePushforward_val, finiteCyclePushforward_comp_apply]
      refine (finiteCyclePushforward_congr_map _ _
        (pointAmbientMap_zeroAmbientProjection q) a.val).trans ?_
      rw [← finiteCyclePushforward_comp_apply]
      exact congrArg (finiteCyclePushforward (pointAmbientMap (k := k) q))
        (zeroProjection_cycle E q α)

/-- Every rational graph transfers by the full fundamental cycle of the finite field point. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/Corestriction.lean:218-239"
  "adaptation" "Native signed cycle of the actual finite point"]
theorem pointPushforward_graph_fundamental (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q) :
    (pointPushforward (k := k) q ((Cor.graphFunctor E).map f)).val =
      finiteCyclePushforward (finitePointMap (k := k) q f)
        (AlgebraicCycle.fundamentalCycle (Spec (.of E))) := by
  let A := SmoothSite.base (Spec (.of E))
  let B := target E q
  have := isClosedImmersion_correspondenceGraphMap A.hom B.hom f.left (MorphismProperty.Over.w f)
  let : IsNoetherian ((𝟭 Scheme).obj A.left) := inferInstanceAs (IsNoetherian (Spec (.of E)))
  let : IsReduced ((𝟭 Scheme).obj A.left) := inferInstanceAs (IsReduced (Spec (.of E)))
  have h := finiteCyclePushforward_fundamentalCycle_graph A.hom B.hom f.left
    (MorphismProperty.Over.w f)
  rw [pointPushforward_val]
  unfold finitePointMap
  rw [← finiteCyclePushforward_comp_apply]
  exact congrArg (finiteCyclePushforward (pointAmbientMap (k := k) q)) h.symm

/-- The integral source field point contributes one prime with its actual image residue degree. -/
theorem pointPushforward_graph_val (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q) :
    (pointPushforward (k := k) q ((Cor.graphFunctor E).map f)).val =
      finiteCyclePushforward (finitePointMap (k := k) q f)
        (single (genericPoint (Spec (.of E))) 1) := by
  rw [pointPushforward_graph_fundamental]
  apply congrArg (finiteCyclePushforward (finitePointMap (k := k) q f))
  refine (AlgebraicCycle.fundamentalCycle_eq_single_genericPoint _).trans ?_
  exact congrArg (fun d : DecidableEq (Spec (.of E)) =>
    @single (Spec (.of E)) _ ℤ d _ (genericPoint (Spec (.of E))) 1) (Subsingleton.elim _ _)

/-- Every signed point class transfers by its original finite pushforward. -/
theorem corestriction_cycleClass (q : ℕ) (α : point E ⟶ DiagonalCycleSymbols.target E q) :
    corestriction (k := k) q (cycleClass E q α) =
      cycleClass k q (pointPushforward (k := k) q α) := by
  let a : Cor.mk (source E 0) ⟶ Cor.mk (target E q) := WeightOne.zeroSimplexProjection E ≫ α
  rw [cycleClass_apply, corestriction_singularClass]
  refine (congrArg (singularClass k q)
    (reducedPushforward_quotient (k := k) 0 q a)).trans ?_
  rw [cycleClass_apply]
  exact congrArg (fun b : Cor.mk (source k 0) ⟶ Cor.mk (target k q) =>
    singularClass k q ((toReducedTorus k q).hom.app _ (ULift.up b)))
      (zeroProjection_pointPushforward q α).symm

/-- Signed point-cycle representatives determine the raw transfer. -/
theorem corestriction_unique (q : ℕ)
    (f : (motivicRawBaseComplex E q).homology q →+ (motivicRawBaseComplex k q).homology q)
    (hf : ∀ α : point E ⟶ DiagonalCycleSymbols.target E q,
      f (cycleClass E q α) = cycleClass k q (pointPushforward (k := k) q α)) :
    f = corestriction (k := k) (E := E) q := by
  ext x
  obtain ⟨α, rfl⟩ := cycleClass_surjective E q x
  exact (hf α).trans (corestriction_cycleClass q α).symm

/-- The transfer of a rational symbol is the class of its entire finite graph cycle. -/
theorem corestriction_graphSymbol (q : ℕ) (a : Fin q → Eˣ) :
    corestriction (k := k) q (graphSymbol E q a) =
      cycleClass k q (pointPushforward (k := k) q
        ((Cor.graphFunctor E).map (rationalTuple E q a))) :=
  corestriction_cycleClass q _

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Derived transfer retains the same native signed representative. -/
theorem integralCorestriction_cycleClass (q : ℕ) (α : point E ⟶ DiagonalCycleSymbols.target E q) :
    integralCorestriction (k := k) q
      ((motivicRawBaseEvaluationComparison E q q).symm (cycleClass E q α)) =
    (motivicRawBaseEvaluationComparison k q q).symm
      (cycleClass k q (pointPushforward (k := k) q α)) := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [integralCorestriction_comparison, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, corestriction_cycleClass]

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction
