/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleFace

/-!
# Scalar extension of diagonal cycles

The pullback of a native admissible prime is the full cycle of its actual
scheme-theoretic inverse image. The scalar map keeps the generic stalk
length of every new component and extends by the original signed coefficients.
The two simplex degrees used for diagonal cohomology have finite flat supports.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/Field/Cycle.lean:99-185`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange

open _root_.AlgebraicGeometry.Scheme
open DiagonalFiniteCyclePushforward

/-- A proper closed-support cycle has the native whole fundamental coefficients
when every component has the specified grade. -/
theorem val_cycleAssociatedToClosedSubscheme_eq_finitePushforward_fundamental
    (C : ChowSituation.{u}) {P X : Scheme.{u}} [IsNoetherian P]
    (s : X ⟶ C.S) [LocallyOfFiniteType s] (i : P ⟶ X) [IsClosedImmersion i]
    (d : ℤ)
    (hgrade : ∀ z : genericPoints P, relativeDimension C.dimensionFunction s (i z.val) = d) :
    (cycleAssociatedToClosedSubscheme C s i d).val =
      finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle P) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases h : ∃ z : genericPoints P, i z.val = x
  · obtain ⟨z, rfl⟩ := h
    rw [cycleAssociatedToClosedSubscheme_apply C s i d z (hgrade z),
      componentMultiplicity_eq_length_stalk,
      finiteCyclePushforward_apply_of_isClosedImmersion,
      AlgebraicCycle.fundamentalCycle_apply_generic P z]
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C s i d x
        (fun ⟨z, hz, _⟩ => h ⟨z, hz⟩)]
    by_contra hn
    obtain ⟨z, hz, rfl⟩ := finiteCyclePushforward_support_subset i _ (Ne.symm hn)
    exact h ⟨⟨z, AlgebraicCycle.support_fundamentalCycle_subset P hz⟩, rfl⟩

/-- A quasi-compact locally finite type scheme over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_quasiCompact_locallyOfFiniteType
    {P X : Scheme.{u}} [IsNoetherian X] (f : P ⟶ X)
    [QuasiCompact f] [LocallyOfFiniteType f] : IsNoetherian P where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f

section Support

variable {S S' X X' Y Y' : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S'} {g' : Y' ⟶ S'}
  {a : X' ⟶ X} {m : pullback f' g' ⟶ pullback f g}
  (sq : IsPullback m (pullback.fst f' g') (pullback.fst f g) a)

include sq in
/-- The pulled closed support is Cartesian over the actual changed source. -/
theorem supportPullback_projection_isPullback (z : (pullback f g : Scheme.{u})) :
    IsPullback (pullback.fst (integralComponentAt z).subschemeι m)
      (pullback.snd (integralComponentAt z).subschemeι m ≫ pullback.fst f' g')
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g) a :=
  (IsPullback.of_hasPullback (integralComponentAt z).subschemeι m).paste_vert sq

variable [IsNoetherian X'] [IsSeparated g'] [LocallyOfFiniteType g']

/-- The full pullback of an actual finite flat support as a native correspondence. -/
def supportPullbackCycle (z : (pullback f g : Scheme.{u}))
    (hz : IsFiniteCorrespondencePoint f g z)
    (hflat : Flat ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) :
    finiteCorrespondences f' g' := by
  let i := (integralComponentAt z).subschemeι
  let π := pullback.snd i m ≫ pullback.fst f' g'
  let : IsFinite π := MorphismProperty.of_isPullback (supportPullback_projection_isPullback sq z)
    hz.1
  let : Flat π := MorphismProperty.of_isPullback (supportPullback_projection_isPullback sq z)
    hflat
  let : IsNoetherian (pullback i m : Scheme.{u}) :=
    isNoetherian_of_quasiCompact_locallyOfFiniteType π
  exact finiteFlatSpanFundamental f' g' (pullback.snd i m)

/-- Scalar pullback preserves the actual local multiplicity of every new support. -/
theorem supportPullbackCycle_val (z : (pullback f g : Scheme.{u}))
    (hz : IsFiniteCorrespondencePoint f g z)
    (hflat : Flat ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) :
    let i := (integralComponentAt z).subschemeι
    let π := pullback.snd i m ≫ pullback.fst f' g'
    letI : IsFinite π :=
      MorphismProperty.of_isPullback (supportPullback_projection_isPullback sq z) hz.1
    letI : IsNoetherian (pullback i m : Scheme.{u}) :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType π
    (supportPullbackCycle sq z hz hflat).val =
      finiteCyclePushforward (pullback.snd i m)
        (AlgebraicCycle.fundamentalCycle (pullback i m)) := rfl

/-- Scalar extension of signed cycles, using the full inverse image of each prime. -/
def cyclePullbackAlong
    (hflat : ∀ z : (pullback f g : Scheme.{u}), IsFiniteCorrespondencePoint f g z →
      Flat ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) :
    finiteCorrespondences f g →+ finiteCorrespondences f' g' :=
  liftFiniteCorrespondence f g (fun z hz => supportPullbackCycle sq z hz (hflat z hz))

/-- Scalar extension of a prime uses its original whole support fiber. -/
theorem cyclePullbackAlong_single
    (hflat : ∀ z : (pullback f g : Scheme.{u}), IsFiniteCorrespondencePoint f g z →
      Flat ((integralComponentAt z).subschemeι ≫ pullback.fst f g))
    (z : (pullback f g : Scheme.{u})) (hz : IsFiniteCorrespondencePoint f g z) :
    cyclePullbackAlong sq hflat (singleFiniteCorrespondence f g z hz 1) =
      supportPullbackCycle sq z hz (hflat z hz) := by
  rw [cyclePullbackAlong, liftFiniteCorrespondence_single, one_zsmul]

end Support

section Simplex

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The actual scalar ambient map is Cartesian over the changed simplex source. -/
theorem ambientMap_fst_isPullback (r q : ℕ) :
    IsPullback (ambientMap (k := k) (E := L) r q)
      (pullback.fst (source L r).hom (target L q).hom)
      (pullback.fst (source k r).hom (target k q).hom)
      (DiagonalFiniteCyclePushforward.sourceMap (k := k) (E := L) r) :=
  (ambientMap_isPullback (k := k) (E := L) r q).of_bot (ambientMap_fst r q)
    (sourceMap_isPullback r)

/-- The native simplex source is Noetherian over its coefficient field. -/
theorem simplexSource_isNoetherian (F : Type u) [Field F] (r : ℕ) :
    IsNoetherian ((𝟭 Scheme).obj (source F r).left) := by
  let f : (source F r).left ⟶ Spec (.of F) := (source F r).hom
  exact isNoetherian_of_quasiCompact_locallyOfFiniteType f

/-- Every admissible prime is finite flat over the original zero or one simplex. -/
theorem supportProjection_flat (F : Type u) [Field F] (r : Fin 2) (q : ℕ)
    (z : ambient F r q) (hz : IsFiniteCorrespondencePoint (source F r).hom (target F q).hom z) :
    Flat ((integralComponentAt z).subschemeι ≫
      pullback.fst (source F r).hom (target F q).hom) := by
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨j, rfl⟩
  · let π := (integralComponentAt z).subschemeι ≫
      pullback.fst (source F 0).hom (target F q).hom
    let : Subsingleton (Spec (.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    have : Flat (π ≫ (sourceChart0 F).hom) :=
      Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral (Y := Spec (.of F)) _
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Flat) π (sourceChart0 F).hom).mp
      inferInstance
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    let π := (integralComponentAt z).subschemeι ≫
      pullback.fst (source F 1).hom (target F q).hom
    let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
    let : IsFinite π := hz.1
    let : Surjective π := by
      have hr : Set.range π ∈ irreducibleComponents (source F 1).left := hz.2
      rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hr
      exact ⟨Set.range_eq_univ.mp hr⟩
    have : Flat (π ≫ (sourceChart1 F).hom) :=
      flat_finite_surjective_polynomial (π ≫ (sourceChart1 F).hom)
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Flat) π (sourceChart1 F).hom).mp
      inferInstance

/-- The signed field restriction in the two simplex degrees needed by the diagonal. -/
def cyclePullback (r : Fin 2) (q : ℕ) :
    finiteCorrespondences (source k r).hom (target k q).hom →+
      finiteCorrespondences (source L r).hom (target L q).hom := by
  letI : IsNoetherian ((𝟭 Scheme).obj (source L (r : ℕ)).left) := simplexSource_isNoetherian L r
  exact cyclePullbackAlong (X' := ((𝟭 Scheme).obj (source L (r : ℕ)).left))
    (ambientMap_fst_isPullback (k := k) (L := L) r q)
    (supportProjection_flat k r q)

/-- The changed simplex prime is the full scalar pullback of its actual closed support. -/
theorem cyclePullback_single (r : Fin 2) (q : ℕ) (z : ambient k r q)
    (hz : IsFiniteCorrespondencePoint (source k r).hom (target k q).hom z) :
    letI : IsNoetherian ((𝟭 Scheme).obj (source L (r : ℕ)).left) :=
      simplexSource_isNoetherian L r
    cyclePullback (k := k) (L := L) r q (singleFiniteCorrespondence _ _ z hz 1) =
      supportPullbackCycle (X' := ((𝟭 Scheme).obj (source L (r : ℕ)).left))
        (ambientMap_fst_isPullback (k := k) (L := L) r q) z hz
        (supportProjection_flat k r q z hz) := by
  let : IsNoetherian ((𝟭 Scheme).obj (source L (r : ℕ)).left) := simplexSource_isNoetherian L r
  exact cyclePullbackAlong_single (X' := ((𝟭 Scheme).obj (source L (r : ℕ)).left))
    (ambientMap_fst_isPullback (k := k) (L := L) r q)
    (supportProjection_flat k r q) z hz

end Simplex

end AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange
