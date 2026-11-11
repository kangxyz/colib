/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionPoints
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChangeCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitCycles
public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles

/-!
# Grade-zero scalar pullback of diagonal point cycles

The full inverse-image cycle of each native finite point support agrees with
the grade-zero Chow pullback. The comparison uses the same closed support
and all of its generic stalk lengths in both the point ambient and the
actual zero-simplex ambient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange

open _root_.AlgebraicGeometry.Scheme
open DiagonalCorestriction DiagonalTopDegree DiagonalFieldChange
open DiagonalFiniteCyclePushforward (scalarMap torusMap_isPullback productMap_isPullback)

/-- The projection of the native point-times-torus ambient to the base point. -/
abbrev pointAmbientStructure (F : Type u) [Field F] (q : ℕ) :
    pointAmbient F q ⟶ Spec (.of F) :=
  pullback.fst (SmoothSite.base (Spec (.of F))).hom
    (DiagonalCycleSymbols.target F q).toSmoothSite.hom

section Ambient

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The original point ambient is Cartesian over the actual scalar morphism. -/
theorem pointAmbientMap_isPullback (q : ℕ) :
    IsPullback (pointAmbientMap (k := k) (E := L) q)
      (pointAmbientStructure L q) (pointAmbientStructure k q) (scalarMap (k := k) (E := L)) := by
  have h : IsPullback (pointAmbientMap (k := k) (E := L) q)
      (pointAmbientStructure L q ≫ 𝟙 (Spec (.of L)))
      (pointAmbientStructure k q ≫ 𝟙 (Spec (.of k))) (scalarMap (k := k) (E := L)) :=
    productMap_isPullback (IsPullback.id_vert (scalarMap (k := k) (E := L)))
      (torusMap_isPullback (k := k) (E := L) q)
  rw [Category.comp_id, Category.comp_id] at h
  exact h

/-- Each original point support is flat over its coefficient field. -/
theorem pointSupport_flat (F : Type u) [Field F] (q : ℕ) (z : pointAmbient F q) :
    Flat ((integralComponentAt z).subschemeι ≫ pointAmbientStructure F q) := by
  let : Subsingleton (Spec (.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral (Y := Spec (.of F)) _

/-- Scalar pullback of signed point correspondences before passing to motivic classes. -/
def pointCycleFieldChange (q : ℕ) :
    (point k ⟶ DiagonalCycleSymbols.target k q) →+
      (point L ⟶ DiagonalCycleSymbols.target L q) := by
  let : IsNoetherian ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of L))).left) :=
    inferInstanceAs (IsNoetherian (Spec (.of L)))
  exact cyclePullbackAlong (X' := ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of L))).left))
    (pointAmbientMap_isPullback (k := k) (L := L) q)
    (fun z _ => pointSupport_flat k q z)

/-- A finite scheme over a field has relative dimension zero at every point. -/
theorem relativeDimension_zero_of_finite (F : Type u) [Field F]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of F)) [IsFinite s] (x : X) :
    relativeDimension (fieldChowSituation F).dimensionFunction s x = 0 := by
  let : Algebra ((Spec (.of F)).residueField (s x)) (X.residueField x) :=
    (s.residueFieldMap x).hom.toAlgebra
  let : Module.Finite ((Spec (.of F)).residueField (s x)) (X.residueField x) :=
    residueField_finite_of_locallyQuasiFinite s x
  rw [relativeDimension_apply_add_residueTrdeg, fieldChowSituation_dimensionFunction_eq_zero,
    zero_add]
  change ((Algebra.trdeg ((Spec (.of F)).residueField (s x))
    (X.residueField x)).toNat : ℤ) = 0
  rw [trdeg_eq_zero]
  change ((Cardinal.toNat ((0 : ℕ) : Cardinal)) : ℤ) = 0
  rw [Cardinal.toNat_natCast, Nat.cast_zero]

/-- Every point of a closed support finite over the field has ambient grade zero. -/
theorem relativeDimension_zero_of_finite_closedSupport (F : Type u) [Field F]
    {P X : Scheme.{u}} (s : X ⟶ Spec (.of F)) (i : P ⟶ X) [IsClosedImmersion i]
    [IsFinite (i ≫ s)] (x : P) :
    relativeDimension (fieldChowSituation F).dimensionFunction s (i x) = 0 :=
  (relativeDimension_comp_closedImmersion (fieldChowSituation F).dimensionFunction i s x).symm.trans
    (relativeDimension_zero_of_finite F (i ≫ s) x)

/-- Every finite closed support over the coefficient field has grade at most zero. -/
theorem schemeDeltaDimension_le_zero_of_finite_closedSupport (F : Type u) [Field F]
    {P X : Scheme.{u}} (s : X ⟶ Spec (.of F)) [LocallyOfFiniteType s]
    (i : P ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ s)] :
    schemeDeltaDimension (fieldChowSituation F) (i ≫ s) ≤ ((0 : ℤ) : EInt) :=
  schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation F) s i
    (fun x => le_of_eq (relativeDimension_zero_of_finite_closedSupport F s i x))

/-- In grade zero the cycle of a finite closed support keeps its full fundamental cycle. -/
theorem val_gradeZero_finite_closedSupport (F : Type u) [Field F]
    {P X : Scheme.{u}} [IsNoetherian P] (s : X ⟶ Spec (.of F)) [LocallyOfFiniteType s]
    (i : P ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ s)] :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation F) s i 0).val =
      finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle P) :=
  val_cycleAssociatedToClosedSubscheme_eq_finitePushforward_fundamental
    (fieldChowSituation F) s i 0
    (fun x => relativeDimension_zero_of_finite_closedSupport F s i x.val)

/-- Correspondences from a source finite over the field give native grade-zero cycles. -/
def cycleGradeZero {F : Type u} [Field F] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) (g : Y ⟶ Spec (.of F)) [IsFinite f]
    (s : pullback f g ⟶ Spec (.of F)) [LocallyOfFiniteType s]
    (hs : pullback.fst f g ≫ f = s) :
    finiteCorrespondences f g →+ CycleGroup (fieldChowSituation F) s 0 where
  toFun α := ⟨α.val, (mem_cyclesOfDimension_iff_forall_point _ _ _ _).mpr (fun z hz => by
    let i := (integralComponentAt z).subschemeι
    let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
    let : IsFinite (i ≫ pullback.fst f g) := (α.property.2 z hz).1
    let : IsFinite (i ≫ s) := by
      rw [← hs, ← Category.assoc]
      infer_instance
    have h := relativeDimension_zero_of_finite_closedSupport F s
      i (genericPoint (integralComponentAt z).subscheme)
    rwa [subschemeι_genericPoint_integralComponentAt] at h)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem cyclePullbackAlong_gradeZero_val
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of L)} {g' : Y' ⟶ Spec (.of L)}
    [IsFinite f] [IsFinite f'] [IsNoetherian X'] [IsSeparated g'] [LocallyOfFiniteType g']
    {a : X' ⟶ X} {p : pullback f' g' ⟶ pullback f g}
    (sqproj : IsPullback p (pullback.fst f' g') (pullback.fst f g) a)
    {s : pullback f g ⟶ Spec (.of k)} {s' : pullback f' g' ⟶ Spec (.of L)}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s']
    (hs : pullback.fst f g ≫ f = s) (hs' : pullback.fst f' g' ≫ f' = s')
    (sq : IsPullback p s' s (scalarMap (k := k) (E := L)))
    (hflat : ∀ z : (pullback f g : Scheme.{u}), IsFiniteCorrespondencePoint f g z →
      Flat ((integralComponentAt z).subschemeι ≫ pullback.fst f g))
    (α : finiteCorrespondences f g) :
    (cyclePullbackAlong sqproj hflat α).val =
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl s sq
        0 (cycleGradeZero f g s hs α)).val := by
  classical
  let B := fieldExtensionBaseChangeSituation k L
  let bc := baseChangeCyclePullbackOfIsPullback B rfl s sq 0
  let grad := cycleGradeZero f g s hs
  have heq : (finiteCorrespondences f' g').subtype.comp (cyclePullbackAlong sqproj hflat) =
      (cyclesOfDimension (fieldChowSituation L) s' 0).subtype.comp (bc.comp grad) := by
    apply finiteCorrespondences.addHom_ext_one f g
    intro z hz
    let i := (integralComponentAt z).subschemeι
    let j := pullback.snd i p
    let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
    let : IsFinite (i ≫ pullback.fst f g) := hz.1
    let : IsFinite (j ≫ pullback.fst f' g') :=
      MorphismProperty.of_isPullback (supportPullback_projection_isPullback sqproj z) hz.1
    let : IsFinite (i ≫ s) := by rw [← hs, ← Category.assoc]; infer_instance
    let : IsFinite (j ≫ s') := by rw [← hs', ← Category.assoc]; infer_instance
    let : IsNoetherian (integralComponentAt z).subscheme :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (i ≫ s)
    let : IsNoetherian (pullback i p : Scheme.{u}) :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (j ≫ s')
    let γ := singleFiniteCorrespondence f g z hz 1
    have hgrad : grad γ =
        cycleAssociatedToClosedSubscheme (fieldChowSituation k) s i 0 := by
      apply Subtype.ext
      change γ.val = _
      calc
        γ.val = single z 1 := by
          apply Function.locallyFinsuppWithin.ext
          intro x
          by_cases hx : x = z <;> simp [γ, singleFiniteCorrespondence, single_apply, hx]
        _ = _ := by
          rw [val_gradeZero_finite_closedSupport k s i,
            finiteCyclePushforward_fundamentalCycle_integral,
            subschemeι_genericPoint_integralComponentAt]
    have hc : bc (cycleAssociatedToClosedSubscheme B.base s i 0) =
        cycleAssociatedToClosedSubscheme B.baseChange s' j 0 :=
      baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme B rfl s sq i 0
        (schemeDeltaDimension_le_zero_of_finite_closedSupport k s i)
    change (cyclePullbackAlong sqproj hflat γ).val = (bc (grad γ)).val
    calc
      _ = (supportPullbackCycle sqproj z hz (hflat z hz)).val :=
        congrArg (fun β : finiteCorrespondences f' g' => β.val)
          (cyclePullbackAlong_single sqproj hflat z hz)
      _ = finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle (pullback i p)) :=
        supportPullbackCycle_val sqproj z hz (hflat z hz)
      _ = (cycleAssociatedToClosedSubscheme B.baseChange s' j 0).val :=
        (val_gradeZero_finite_closedSupport L s' j).symm
      _ = (bc (cycleAssociatedToClosedSubscheme B.base s i 0)).val :=
        congrArg Subtype.val hc.symm
      _ = _ := congrArg (fun β => (bc β).val) hgrad.symm
  exact DFunLike.congr_fun heq α

/-- A native signed point correspondence lies in the original grade-zero Chow cycle group. -/
def pointCycleGrade (F : Type u) [Field F] (q : ℕ) :
    (point F ⟶ DiagonalCycleSymbols.target F q) →+
      CycleGroup (fieldChowSituation F) (pointAmbientStructure F q) 0 :=
  cycleGradeZero (𝟙 _) (SmoothSite.torusPower (Spec (.of F)) q).hom
    (pointAmbientStructure F q) (Category.comp_id _)

/-- The scalar extension of the original point cycles is the native Chow flat pullback. -/
theorem pointCycleFieldChange_val (q : ℕ) (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    (pointCycleFieldChange (k := k) (L := L) q α).val =
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl
        (pointAmbientStructure k q) (pointAmbientMap_isPullback (k := k) (L := L) q)
        0 (pointCycleGrade k q α)).val := by
  let : IsFinite (SmoothSite.base (Spec (.of k))).hom :=
    inferInstanceAs (IsFinite (𝟙 (Spec (.of k))))
  let : IsFinite (SmoothSite.base (Spec (.of L))).hom :=
    inferInstanceAs (IsFinite (𝟙 (Spec (.of L))))
  let : IsNoetherian ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of L))).left) :=
    inferInstanceAs (IsNoetherian (Spec (.of L)))
  exact cyclePullbackAlong_gradeZero_val
    (X' := ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of L))).left))
    (pointAmbientMap_isPullback (k := k) (L := L) q)
    (Category.comp_id _) (Category.comp_id _)
    (pointAmbientMap_isPullback (k := k) (L := L) q) (fun z _ => pointSupport_flat k q z) α

end Ambient

section ZeroSimplex

open DiagonalFiniteCyclePushforward (source target ambient ambientMap ambientMap_isPullback)

/-- The native simplex-times-torus structure map over the coefficient field. -/
abbrev simplexAmbientStructure (F : Type u) [Field F] (r q : ℕ) :
    ambient F r q ⟶ Spec (.of F) :=
  pullback.fst (source F r).hom (target F q).hom ≫ (source F r).hom

/-- The original zero-simplex structure is finite over its coefficient field. -/
theorem sourceZero_isFinite (F : Type u) [Field F] : IsFinite (source F 0).hom := by
  have h := MorphismProperty.Over.w (zeroProjection F)
  change (zeroProjection F).left ≫ 𝟙 _ = (source F 0).hom at h
  rw [Category.comp_id] at h
  rw [← h]
  infer_instance

/-- Native zero-simplex correspondences have grade zero. -/
def simplexZeroCycleGrade (F : Type u) [Field F] (q : ℕ) :
    finiteCorrespondences (source F 0).hom (target F q).hom →+
      CycleGroup (fieldChowSituation F) (simplexAmbientStructure F 0 q) 0 := by
  letI : IsFinite (source F 0).hom := sourceZero_isFinite F
  exact cycleGradeZero (source F 0).hom (target F q).hom (simplexAmbientStructure F 0 q) rfl

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Scalar pullback in the zero simplex is the native grade-zero flat Chow pullback. -/
theorem cyclePullback_zero_val (q : ℕ)
    (α : finiteCorrespondences (source k 0).hom (target k q).hom) :
    (cyclePullback (k := k) (L := L) 0 q α).val =
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl
        (simplexAmbientStructure k 0 q) (ambientMap_isPullback (k := k) (E := L) 0 q)
        0 (simplexZeroCycleGrade k q α)).val := by
  let : IsFinite (source k 0).hom := sourceZero_isFinite k
  let : IsFinite (source L 0).hom := sourceZero_isFinite L
  let : IsNoetherian ((𝟭 Scheme).obj (source L 0).left) :=
    simplexSource_isNoetherian L 0
  exact cyclePullbackAlong_gradeZero_val (X' := ((𝟭 Scheme).obj (source L 0).left))
    (ambientMap_fst_isPullback (k := k) (L := L) 0 q) rfl rfl
    (ambientMap_isPullback (k := k) (E := L) 0 q) (supportProjection_flat k 0 q) α

end ZeroSimplex

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange
