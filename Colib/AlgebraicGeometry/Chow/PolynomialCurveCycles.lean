/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.GraphNaturality
public import Mathlib.Data.Fin.VecNotation

/-!
# Native polynomial cycles with an invertible complementary coordinate

The native polynomial quotient cycle lifts to the open where the complement of
the forward Laurent coordinate is invertible. The lift is unique coefficient
by coefficient and keeps all lengths in the whole polynomial quotient.
The actual map from that open to the two-fold torus records both coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] Stacks.Chow.isIntegral_integralComponentAt

universe u

namespace AlgebraicGeometry.PolynomialCurveCycles

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

/-- The underlying scheme of the original smooth-site torus. -/
abbrev torusScheme : Scheme.{u} := multiplicativeGroupBaseChange (Spec (.of k))

private instance : IsAffine (torusScheme k) := by
  change IsAffine (pullback
    (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from (Spec (.of k))))
  infer_instance

/-- The complement of the native forward Laurent coordinate. -/
def complementEquation : Γ(torusScheme k, ⊤) :=
  1 - (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val

/-- The actual principal open on which the complementary coordinate is invertible. -/
def complementOpen : (torusScheme k).Opens :=
  (torusScheme k).basicOpen (complementEquation k)

/-- The same open in the existing smooth site. -/
def complementObject : SmoothSite (Spec (.of k)) := by
  let j : (complementOpen k).toScheme ⟶ (multiplicativeGroupObject (Spec (.of k))).left :=
    (complementOpen k).ι
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (complementOpen k).ι)
  let : IsAffine (complementOpen k).toScheme :=
    inferInstanceAs (IsAffine ((torusScheme k).basicOpen (complementEquation k)))
  exact SmoothSite.mk (j ≫ (multiplicativeGroupObject (Spec (.of k))).hom)

/-- Inclusion of the open in the original multiplicative group. -/
def openInclusion : complementObject k ⟶ multiplicativeGroupObject (Spec (.of k)) :=
  homMk (complementOpen k).ι rfl

instance : IsOpenImmersion (openInclusion k).left :=
  inferInstanceAs (IsOpenImmersion (complementOpen k).ι)

/-- Pulling back the complement equation to the open gives an actual unit. -/
def complementUnit : (Γ((complementObject k).left, ⊤))ˣ := by
  have h : IsUnit ((openInclusion k).left.appTop (complementEquation k)) := by
    change IsUnit ((algebraMap (Γ(torusScheme k, ⊤))
      (Γ((torusScheme k).basicOpen (complementEquation k), ⊤))) (complementEquation k))
    exact IsLocalization.Away.algebraMap_isUnit (complementEquation k)
  exact h.unit

@[simp] theorem complementUnit_val :
    (complementUnit k).val = (openInclusion k).left.appTop (complementEquation k) :=
  IsUnit.unit_spec _

/-- The genuine second torus coordinate on the open. -/
def complementCoordinate : complementObject k ⟶ multiplicativeGroupObject (Spec (.of k)) :=
  homMk (nativeTorusPoint (complementObject k).hom (complementUnit k)).left
    (nativeTorusPoint_over _ _)

/-- The two literal coordinates `(x, 1 - x)` on the same open. -/
def pairMap : complementObject k ⟶ torusPower (Spec (.of k)) 2 :=
  torusPowerLift (Spec (.of k)) 2 ![openInclusion k, complementCoordinate k]

/-- A unit complementary coordinate forces the whole image into the native open. -/
theorem range_subset_of_isUnit {P : Scheme.{u}} (f : P ⟶ torusScheme k)
    (h : IsUnit (f.appTop (complementEquation k))) :
    Set.range f ⊆ Set.range (openInclusion k).left := by
  change Set.range f ⊆ Set.range (complementOpen k).ι
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change x ∈ f ⁻¹ᵁ (torusScheme k).basicOpen (complementEquation k)
  rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ h]
  trivial

/-- A torus point whose complement is a unit has its original lift to the open. -/
def liftPoint {X : SmoothSite (Spec (.of k))}
    (f : X ⟶ multiplicativeGroupObject (Spec (.of k)))
    (h : IsUnit (f.left.appTop (complementEquation k))) : X ⟶ complementObject k :=
  homMk (IsOpenImmersion.lift (openInclusion k).left f.left (range_subset_of_isUnit k f.left h))
    (by
      change (IsOpenImmersion.lift (openInclusion k).left f.left _) ≫
        (openInclusion k).left ≫ (multiplicativeGroupObject (Spec (.of k))).hom = X.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact MorphismProperty.Over.w f)

@[reassoc]
theorem liftPoint_inclusion {X : SmoothSite (Spec (.of k))}
    (f : X ⟶ multiplicativeGroupObject (Spec (.of k)))
    (h : IsUnit (f.left.appTop (complementEquation k))) :
    liftPoint k f h ≫ openInclusion k = f := by
  apply MorphismProperty.Over.Hom.ext
  exact IsOpenImmersion.lift_fac _ _ _

private theorem graphTargetMap_isOpenImmersion {X Y Z : SmoothSite (Spec (.of k))}
    (j : Y ⟶ Z) [IsOpenImmersion j.left] :
    IsOpenImmersion (Cor.graphTargetMap k X j) := by
  unfold Cor.graphTargetMap
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (𝟙 X.left)) (inferInstance : IsOpenImmersion j.left)
    (by simp) (MorphismProperty.Over.w j).symm

open Classical in
private theorem openGraph_single {X Y Z : SmoothSite (Spec (.of k))}
    (j : Y ⟶ Z) [IsOpenImmersion j.left] (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    ((singleFiniteCorrespondence X.hom Y.hom z hz 1 : Cor.mk X ⟶ Cor.mk Y) ≫
        (Cor.graphFunctor k).map j).val =
      single (Cor.graphTargetMap k X j z) 1 := by
  have := graphTargetMap_isOpenImmersion k (X := X) j
  let r := correspondenceGraphPostcompositionMap X.hom Y.hom Z.hom
    j.left (MorphismProperty.Over.w j) z
  have : IsPreimmersion r := by
    change IsPreimmersion ((integralComponentAt z).subschemeι ≫ Cor.graphTargetMap k X j)
    infer_instance
  let : IsFinite r := isFinite_correspondenceGraphPostcompositionMap
    X.hom Y.hom Z.hom j.left (MorphismProperty.Over.w j) z hz
  change (incidenceTorPairing X.hom Y.hom Z.hom
    (singleFiniteCorrespondence X.hom Y.hom z hz 1)
    (graphCorrespondenceOfComponents Y.hom Z.hom j.left (MorphismProperty.Over.w j)
      (Cor.finite_genericPoints k (Cor.mk Y)))).val = _
  rw [incidenceTorPairing_single_graph_right_val]
  change finiteCyclePushforward r (single (genericPoint (integralComponentAt z).subscheme) 1) = _
  rw [finiteCyclePushforward_single, residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]
  exact congrArg (fun w : pullback (C := Scheme) X.hom Z.hom => single w (1 : ℤ))
    (correspondenceGraphPostcompositionMap_genericPoint
      X.hom Y.hom Z.hom j.left (MorphismProperty.Over.w j) z)

private def coefficient {A : Scheme.{u}} (z : A) : AlgebraicCycle A ℤ →+ ℤ where
  toFun c := c z
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Open target graphs preserve each coefficient at its actual image point. -/
theorem openGraph_coefficient {X Y Z : SmoothSite (Spec (.of k))}
    (j : Y ⟶ Z) [IsOpenImmersion j.left] (α : Cor.mk X ⟶ Cor.mk Y)
    (x : pullback (C := Scheme) X.hom Y.hom) :
    (α ≫ (Cor.graphFunctor k).map j).val (Cor.graphTargetMap k X j x) = α.val x := by
  classical
  let m := Cor.graphTargetMap k X j
  have : IsOpenImmersion m := graphTargetMap_isOpenImmersion k (X := X) j
  let F := (coefficient (m x)).comp ((finiteCorrespondences X.hom Z.hom).subtype.comp
    (Preadditive.rightComp (Cor.mk X) ((Cor.graphFunctor k).map j)))
  let G := (coefficient x).comp (finiteCorrespondences X.hom Y.hom).subtype
  have h : F = G := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    change ((singleFiniteCorrespondence X.hom Y.hom z hz 1 : Cor.mk X ⟶ Cor.mk Y) ≫
      (Cor.graphFunctor k).map j).val (m x) = (single z (1 : ℤ)) x
    rw [openGraph_single k j z hz]
    by_cases h : x = z
    · subst x
      simp [m, single_apply]
    · have hm : m x ≠ m z := fun e => h (m.isOpenEmbedding.injective e)
      change (single (m z) (1 : ℤ)) (m x) = (single z (1 : ℤ)) x
      simp [single_apply, hm, h]
  exact DFunLike.congr_fun h α

/-- The open target lift of a signed correspondence is unique. -/
theorem openGraph_injective {X Y Z : SmoothSite (Spec (.of k))}
    (j : Y ⟶ Z) [IsOpenImmersion j.left] :
    Function.Injective (fun α : Cor.mk X ⟶ Cor.mk Y => α ≫ (Cor.graphFunctor k).map j) := by
  intro α β h
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact (openGraph_coefficient k j α x).symm.trans
    ((congrArg (fun γ : Cor.mk X ⟶ Cor.mk Z => γ.val (Cor.graphTargetMap k X j x)) h).trans
      (openGraph_coefficient k j β x))

variable {k} {R : Type u} [CommRing R]

/-- A unit evaluation at one makes the actual complement of the quotient root invertible. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/RingTheory/Polynomial/Interpolation/TwoUnitFamily.lean:35-53"
  "adaptation" "The complement is invertible in the whole monic quotient"]
theorem isUnit_one_sub_root (p : R[X]) (h1 : IsUnit (p.eval 1)) :
    IsUnit (1 - AdjoinRoot.root p) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := p) (a := (1 : R))
  have h := congrArg (AdjoinRoot.mk p) hq
  simp only [map_sub, map_mul, AdjoinRoot.mk_self, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    zero_sub, map_one] at h
  have hm : (1 - AdjoinRoot.root p) * AdjoinRoot.mk p q = AdjoinRoot.of p (p.eval 1) := by
    linear_combination h
  have hu : IsUnit ((1 - AdjoinRoot.root p) * AdjoinRoot.mk p q) := by
    rw [hm]
    exact h1.map (AdjoinRoot.of p)
  exact (IsUnit.mul_iff.mp hu).1

private theorem polynomialPoint_range (f : Spec (.of R) ⟶ Spec (.of k))
    (p : R[X]) (h0 : IsUnit (p.coeff 0)) (h1 : IsUnit (p.eval 1)) :
    Set.range (NativeTorusPolynomial.torusPoint f p h0).left ⊆
      Set.range (openInclusion k).left := by
  apply range_subset_of_isUnit k
  apply (isUnit_map_iff
    (Scheme.ΓSpecIso (.of (AdjoinRoot p))).commRingCatIsoToRingEquiv _).mp
  change IsUnit ((Scheme.ΓSpecIso (.of (AdjoinRoot p))).hom
    ((NativeTorusPolynomial.torusPoint f p h0).left.appTop (complementEquation k)))
  rw [complementEquation, map_sub, map_one, map_sub, map_one]
  change IsUnit (1 - (NativeTorusPolynomial.coordinateUnit f p h0 : AdjoinRoot p))
  rw [NativeTorusPolynomial.coordinateUnit_val]
  exact isUnit_one_sub_root p h1

variable [IsNoetherianRing R] (f : Spec (.of R) ⟶ Spec (.of k))
  [Smooth f] [IsSeparated f] [QuasiCompact f]

/-- Every signed prime of the whole polynomial quotient lifts to the native open. -/
theorem polynomialCycle_exists_openLift (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) (h1 : IsUnit (p.eval 1)) :
    ∃ β : Cor.mk (mk f) ⟶ Cor.mk (complementObject k),
      β ≫ (Cor.graphFunctor k).map (openInclusion k) =
        NativeTorusPolynomial.polynomialCycle f p hp h0 := by
  classical
  let c := NativeTorusPolynomial.polynomialCycle f p hp h0
  let j := NativeTorusPolynomial.inclusion f p h0
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) := NativeTorusPolynomial.quotient_isNoetherian p
  let : IsClosedImmersion j := NativeTorusPolynomial.inclusion_isClosedImmersion f p h0
  have hLift (z : c.property.1.toFinset) :
      ∃ β : Cor.mk (mk f) ⟶ Cor.mk (complementObject k),
        β ≫ (Cor.graphFunctor k).map (openInclusion k) =
          singleFiniteCorrespondence f (torusScheme k ↘ Spec (.of k)) z.val
            (c.property.2 z.val (by
              simpa only [Set.Finite.mem_toFinset, Function.locallyFinsuppWithin.support,
                Function.mem_support] using z.property))
            1 := by
    have hz : z.val ∈ c.val.support :=
      (Set.Finite.mem_toFinset c.property.1).mp z.property
    have hz' : z.val ∈
        (finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle
          (Spec (.of (AdjoinRoot p))))).support := by
      exact (NativeTorusPolynomial.polynomialCycle_val f p hp h0) ▸ hz
    obtain ⟨v, _, hv⟩ := finiteCyclePushforward_support_subset j _ hz'
    have hc : closure ({z.val} : Set (NativeTorusPolynomial.ambient f)) ⊆ Set.range j :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨v, hv⟩)
        j.isClosedEmbedding.isClosed_range
    have hsub : Set.range ((integralComponentAt z.val).subschemeι ≫
        pullback.snd f (torusScheme k ↘ Spec (.of k))) ⊆
        Set.range (openInclusion k).left := by
      rintro _ ⟨t, rfl⟩
      have hcl : (integralComponentAt z.val).subschemeι t ∈
          closure ({z.val} : Set (NativeTorusPolynomial.ambient f)) := by
        rw [← coe_support_integralComponentAt, ← (integralComponentAt z.val).range_subschemeι]
        exact ⟨t, rfl⟩
      obtain ⟨v', hv'⟩ := hc hcl
      apply polynomialPoint_range f p h0 h1
      refine ⟨v', ?_⟩
      have h := congrArg (fun w : NativeTorusPolynomial.ambient f =>
        pullback.snd f (torusScheme k ↘ Spec (.of k)) w) hv'
      exact (congrArg (fun g => g v') (NativeTorusPolynomial.inclusion_snd f p h0)).symm.trans h
    exact Cor.exists_graph_factorization_of_range_subset k
      (W := mk f) (V := complementObject k) (Y := multiplicativeGroupObject (Spec (.of k)))
      z.val (c.property.2 z.val hz) (openInclusion k) hsub
  choose β hβ using hLift
  refine ⟨∑ z : c.property.1.toFinset, c.val z.val • β z, ?_⟩
  rw [Preadditive.sum_comp]
  refine (Finset.sum_congr rfl (fun z _ => ?_)).trans
    (finiteCorrespondence_eq_sum_signedSingles f (torusScheme k ↘ Spec (.of k)) c).symm
  rw [Preadditive.zsmul_comp, hβ]
  exact (singleFiniteCorrespondence_eq_zsmul f (torusScheme k ↘ Spec (.of k))
    z.val _ (c.val z.val)).symm

/-- The whole native polynomial cycle with both units, uniquely lifted to the open. -/
def openPolynomialCycle (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) : Cor.mk (mk f) ⟶ Cor.mk (complementObject k) :=
  (polynomialCycle_exists_openLift f p hp h0 h1).choose

/-- Projection to the first torus preserves the full original polynomial cycle. -/
@[reassoc]
theorem openPolynomialCycle_inclusion (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) :
    openPolynomialCycle f p hp h0 h1 ≫ (Cor.graphFunctor k).map (openInclusion k) =
      NativeTorusPolynomial.polynomialCycle f p hp h0 :=
  (polynomialCycle_exists_openLift f p hp h0 h1).choose_spec

/-- The actual native correspondence of the whole quotient with coordinates `(x, 1 - x)`. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightTwo/CubicBoundary.lean:144-169,358-395"
  "adaptation" "The whole polynomial cycle followed by the actual complementary-coordinate graph"]
def polynomialCurveCycle (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 2) :=
  openPolynomialCycle f p hp h0 h1 ≫ (Cor.graphFunctor k).map (pairMap k)

end AlgebraicGeometry.PolynomialCurveCycles
