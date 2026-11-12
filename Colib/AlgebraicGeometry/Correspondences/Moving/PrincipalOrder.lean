/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic
public import Colib.AlgebraicGeometry.Morphisms.Smooth.FiniteClosedCurveSupport
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-! # Principal orders as finite correspondences

The native principal cycle weights its actual finite image points by the
residue degrees of the full supports. The whole boundary unit open keeps
each closed support inside the retained smooth curve.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/PrincipalOrder.lean`
and `Motivic/Aglib/AlgebraicGeometry/Cycles/Divisors/PrincipalOrder.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.Cor.PrincipalOrder

open _root_.AlgebraicGeometry.Scheme Stacks.Chow

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  [IsAffine X.left] {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [V.IsQuasiAffine]
  (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (W : C.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set C))
  (r : Γ(C, W)) (hr : IsUnit r)

local notation "c" => principalCycle C (C.germToFunctionField W r)

omit [V.IsQuasiAffine] [IsOpenImmersion j] in
include hr hW in
/-- The full support over a nonzero order point lies in the actual retained open. -/
theorem support_range (x : C) (hx : c x ≠ 0) :
    Set.range (integralComponentAt x).subschemeι ⊆ Set.range j := by
  rw [(integralComponentAt x).range_subschemeι, coe_support_integralComponentAt]
  have hxW : x ∉ W := fun hm => hx (C.ord_of_isUnit hr hm)
  have hc : closure ({x} : Set C) ⊆ (W : Set C)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hxW) W.isOpen.isClosed_compl
  intro y hy
  by_contra hn
  exact hc hy (hW hn)

omit [SmoothOfRelativeDimension 1 (j ≫ q)] in
include hr hW in
/-- The support of a nonzero order is finite over the original base. -/
theorem support_finite (x : C) (hx : c x ≠ 0) :
    IsFinite ((integralComponentAt x).subschemeι ≫ q) :=
  isFinite_closed_support_in_quasiAffine_open q j _ (support_range j W hW r hr x hx)

include hr hW in
/-- Its image is an actual irreducible component of the original base. -/
theorem support_dominates_component (x : C) (hx : c x ≠ 0) :
    Set.range ((integralComponentAt x).subschemeι ≫ q) ∈ irreducibleComponents X.left := by
  let D := (integralComponentAt x).subscheme
  let : IsIntegral D := isIntegral_integralComponentAt x
  let d : D ⟶ C := (integralComponentAt x).subschemeι
  let i := IsOpenImmersion.lift j d (support_range j W hW r hr x hx)
  have hi : i ≫ j = d := IsOpenImmersion.lift_fac ..
  let : IsClosedImmersion (i ≫ j) := hi.symm ▸ inferInstanceAs (IsClosedImmersion d)
  let : IsClosedImmersion i := IsClosedImmersion.of_comp i j
  let : IsFinite (d ≫ q) := support_finite q j W hW r hr x hx
  have he : i ≫ (j ≫ q) = d ≫ q := (Category.assoc i j q).symm.trans (congrArg (· ≫ q) hi)
  let : IsFinite (i ≫ (j ≫ q)) := he.symm ▸ inferInstanceAs (IsFinite (d ≫ q))
  let a := genericPoint D
  have hda : d a = x := genericPointOf_integralComponentAt x
  have hx1 : Order.coheight x = 1 := by
    by_contra hn
    exact hx (C.ord_eq_zero_of_coheight_neq_one hn _)
  have ha : Order.coheight (i a) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion j]
    change Order.coheight ((i ≫ j) a) = 1
    rw [hi, hda]
    exact hx1
  have hg := image_mem_genericPoints_of_coheight_one_finite_closed_support i (j ≫ q) a ha
  have hga : (j ≫ q) (i a) = (d ≫ q) a :=
    congrArg (fun f : D ⟶ X.left => f a) he
  rw [hga] at hg
  have hc : closure ({(d ≫ q) a} : Set X.left) = Set.range (d ≫ q) := by
    simpa only [Set.image_univ, (d ≫ q).isClosedMap.isClosed_range.closure_eq] using
      ((genericPoint_spec D).image (d ≫ q).continuous).def
  rwa [genericPoints, Set.mem_ofPred_eq, hc] at hg

/-- The entire reduced support lifts to the actual retained open. -/
def supportLift (x : C) (hx : c x ≠ 0) : (integralComponentAt x).subscheme ⟶ V :=
  IsOpenImmersion.lift j (integralComponentAt x).subschemeι (support_range j W hW r hr x hx)

omit [V.IsQuasiAffine] in
@[reassoc (attr := simp)]
theorem supportLift_comp (x : C) (hx : c x ≠ 0) :
    supportLift j W hW r hr x hx ≫ j = (integralComponentAt x).subschemeι :=
  IsOpenImmersion.lift_fac ..

instance supportLift_isClosedImmersion (x : C) (hx : c x ≠ 0) :
    IsClosedImmersion (supportLift j W hW r hr x hx) := by
  have : IsClosedImmersion (supportLift j W hW r hr x hx ≫ j) := by
    rw [supportLift_comp]
    infer_instance
  exact IsClosedImmersion.of_comp _ j

/-- The actual retained generic point of the original integral support. -/
def supportPoint (x : C) (hx : c x ≠ 0) : V := by
  let : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  exact supportLift j W hW r hr x hx (genericPoint (integralComponentAt x).subscheme)

omit [V.IsQuasiAffine] in
theorem supportPoint_image (x : C) (hx : c x ≠ 0) :
    j (supportPoint j W hW r hr x hx) = x := by
  let : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  let η := genericPoint (integralComponentAt x).subscheme
  exact (congrArg (fun f : (integralComponentAt x).subscheme ⟶ C => f η)
    (supportLift_comp j W hW r hr x hx)).trans (genericPointOf_integralComponentAt x)

variable (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The actual map of the original support to the source-target product. -/
def supportMap (x : C) (hx : c x ≠ 0) :
    (integralComponentAt x).subscheme ⟶ pullback X.hom Y.hom :=
  pullback.lift ((integralComponentAt x).subschemeι ≫ q)
    (supportLift j W hW r hr x hx ≫ g) (by
      rw [← supportLift_comp j W hW r hr x hx]
      simp only [Category.assoc, hbase])

omit [IsAffine X.left] [IsProper q] [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)] in
@[reassoc (attr := simp)]
theorem supportMap_fst (x : C) (hx : c x ≠ 0) :
    supportMap q j W hW r hr g hbase x hx ≫ pullback.fst X.hom Y.hom =
      (integralComponentAt x).subschemeι ≫ q :=
  pullback.lift_fst _ _ _

omit [IsAffine X.left] [IsProper q] [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)] in
@[reassoc (attr := simp)]
theorem supportMap_snd (x : C) (hx : c x ≠ 0) :
    supportMap q j W hW r hr g hbase x hx ≫ pullback.snd X.hom Y.hom =
      supportLift j W hW r hr x hx ≫ g :=
  pullback.lift_snd _ _ _

instance supportMap_isFinite (x : C) (hx : c x ≠ 0) :
    IsFinite (supportMap q j W hW r hr g hbase x hx) := by
  let : IsFinite ((integralComponentAt x).subschemeι ≫ q) := support_finite q j W hW r hr x hx
  unfold supportMap
  exact isFinite_spanMap _ _ _

/-- The original support image is an admissible prime of the actual product. -/
theorem supportMap_isAdmissible (x : C) (hx : c x ≠ 0) :
    letI : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
    IsFiniteCorrespondencePoint X.hom Y.hom
      (supportMap q j W hW r hr g hbase x hx (genericPoint (integralComponentAt x).subscheme)) := by
  let D := (integralComponentAt x).subscheme
  let : IsIntegral D := isIntegral_integralComponentAt x
  let d : D ⟶ C := (integralComponentAt x).subschemeι
  let f := d ≫ q
  let m := supportMap q j W hW r hr g hbase x hx
  let : IsFinite f := support_finite q j W hW r hr x hx
  let η := genericPoint D
  let b := (integralComponentAt η).subschemeι
  have hm : m ≫ pullback.fst X.hom Y.hom = f := supportMap_fst q j W hW r hr g hbase x hx
  have hfin : IsFinite ((b ≫ m) ≫ pullback.fst X.hom Y.hom) := by
    rw [Category.assoc, hm]
    infer_instance
  have hdom : Set.range ((b ≫ m) ≫ pullback.fst X.hom Y.hom) ∈ irreducibleComponents X.left := by
    rw [Category.assoc, hm]
    have hb : Set.range b = Set.univ := by
      dsimp only [b]
      rw [(integralComponentAt η).range_subschemeι, coe_support_integralComponentAt]
      exact (genericPoint_spec D).def
    change Set.range (⇑f ∘ ⇑b) ∈ irreducibleComponents X.left
    rw [Set.range_comp, hb, Set.image_univ]
    exact support_dominates_component q j W hW r hr x hx
  exact isFiniteCorrespondencePoint_finiteMap X.hom Y.hom m η hfin hdom

/-- The single support term has its original order and finite residue degree. -/
def supportCorrespondence (x : C) (hx : c x ≠ 0) : Cor.mk X ⟶ Cor.mk Y := by
  let : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  let m := supportMap q j W hW r hr g hbase x hx
  let η := genericPoint (integralComponentAt x).subscheme
  exact singleFiniteCorrespondence X.hom Y.hom (m η)
    (supportMap_isAdmissible q j W hW r hr g hbase x hx)
    (c x * (m.residueDegree η : ℤ))

/-- The support correspondence is the single native weighted image prime. -/
theorem supportCorrespondence_val_eq_single (x : C) (hx : c x ≠ 0) :
    letI : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
    let m := supportMap q j W hW r hr g hbase x hx
    let η := genericPoint (integralComponentAt x).subscheme
    (supportCorrespondence q j W hW r hr g hbase x hx).val =
      single (m η) (c x * (m.residueDegree η : ℤ)) :=
  rfl

/-- The principal correspondence of the original rational function, including
the signs and residue degrees of the actual finite image points. -/
def correspondence : Cor.mk X ⟶ Cor.mk Y := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  let h := Function.locallyFinsupp.finite_support c
  exact ∑ x : h.toFinset,
    supportCorrespondence q j W hW r hr g hbase x.val (h.mem_toFinset.mp x.property)

/-- The actual correspondence is the sum of the native supported primes. -/
theorem correspondence_val_sum :
    (correspondence q j W hW r hr g hbase).val =
      ∑ x : (Function.locallyFinsupp.finite_support c).toFinset,
        (supportCorrespondence q j W hW r hr g hbase x.val
          ((Function.locallyFinsupp.finite_support c).mem_toFinset.mp x.property)).val := by
  classical
  unfold correspondence
  exact map_sum (finiteCorrespondences X.hom Y.hom).subtype _ _

end AlgebraicGeometry.Cor.PrincipalOrder
