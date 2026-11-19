/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.PreconnectedRelativeDimension
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-! # Smooth strata of reduced point closures -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme TopologicalSpace
open SmoothSite Stacks.Chow

universe u

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

variable (k : Type u) [Field k]
  (X : SmoothSite (Spec (CommRingCat.of k))) (x : X.left)

/-- The reduced closed subscheme supported on the closure of the point. -/
abbrev pointClosure := (integralComponentAt x).subscheme

/-- The original closed immersion of the reduced closure into the smooth scheme. -/
abbrev pointClosureInclusion : pointClosure k X x ⟶ X.left :=
  (integralComponentAt x).subschemeι

instance : IsIntegral (pointClosure k X x) := isIntegral_integralComponentAt x

/-- The structure map on the original reduced closure. -/
abbrev pointClosureStructure : pointClosure k X x ⟶ Spec (CommRingCat.of k) :=
  pointClosureInclusion k X x ≫ X.hom

/-- The open of the reduced closure induced by an ambient open. -/
abbrev pointClosureOpen (U : X.left.Opens) : (pointClosure k X x).Opens :=
  pointClosureInclusion k X x ⁻¹ᵁ U

private theorem pointClosureGeneric_image :
    pointClosureInclusion k X x (genericPoint (pointClosure k X x)) = x :=
  genericPointOf_integralComponentAt x

/-- The generic point of the reduced closure lies over the given point. -/
def pointClosureGeneric (U : X.left.Opens) (hx : x ∈ U) : (pointClosureOpen k X x U).toScheme :=
  ⟨genericPoint (pointClosure k X x), by
    change pointClosureInclusion k X x (genericPoint (pointClosure k X x)) ∈ U
    rw [pointClosureGeneric_image k X x]
    exact hx⟩

variable {k X x}

/-- An open restriction through the point contains the generic point of the closure. -/
theorem pointClosureOpen_nonempty (U : X.left.Opens) (hx : x ∈ U) :
    Nonempty (pointClosureOpen k X x U).toScheme :=
  ⟨pointClosureGeneric k X x U hx⟩

/-- The restricted closed immersion is over the original point at the generic point. -/
theorem pointClosureInclusion_restrict_generic (U : X.left.Opens) (hx : x ∈ U) :
    (pointClosureInclusion k X x ∣_ U) (pointClosureGeneric k X x U hx) =
      (⟨x, hx⟩ : U.toScheme) := by
  apply U.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact pointClosureGeneric_image k X x

/-- The indicated point is generic on every nonempty restriction through the point. -/
theorem isGenericPoint_pointClosureGeneric (U : X.left.Opens) (hx : x ∈ U) :
    IsGenericPoint (pointClosureGeneric k X x U hx) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  let i := (pointClosureOpen k X x U).ι
  apply i.isOpenEmbedding.isInducing.specializes_iff.mp
  exact genericPoint_specializes (i y)

variable (k X x)

/-- An open containing the generic point of the reduced closure lifts to an
ambient open containing the original point. -/
theorem exists_open_preimage_pointClosure (W : (pointClosure k X x).Opens)
    (hx : genericPoint (pointClosure k X x) ∈ W) :
    ∃ U : X.left.Opens, x ∈ U ∧ pointClosureOpen k X x U = W := by
  let i := pointClosureInclusion k X x
  obtain ⟨V, hV, hpre⟩ := (Scheme.Hom.isClosedEmbedding i).isEmbedding.isInducing.isOpen_iff.1 W.2
  let U : X.left.Opens := ⟨V, hV⟩
  have he : i ⁻¹ᵁ U = W := SetLike.coe_injective hpre
  rw [← he] at hx
  change i (genericPoint (pointClosure k X x)) ∈ U at hx
  exact ⟨U, by simpa only [i, pointClosureGeneric_image] using hx, he⟩

variable [PerfectField k]

/-- An ambient open through the point cuts out the smooth locus on its
original reduced closure. -/
theorem exists_open_preimage_pointClosureSmoothLocus :
    ∃ U : X.left.Opens, x ∈ U ∧
      pointClosureOpen k X x U = (pointClosureStructure k X x).smoothLocus :=
  exists_open_preimage_pointClosure k X x _
    (pointClosureStructure k X x).genericPoint_mem_smoothLocus_of_perfectField

/-- On a sufficiently small neighborhood inside any prescribed neighborhood, the
reduced closure of the point is smooth over the field. -/
theorem exists_smooth_pointClosure_restriction (V : X.left.Opens) (hx : x ∈ V) :
    ∃ U : X.left.Opens, x ∈ U ∧ U ≤ V ∧
      Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom)) := by
  obtain ⟨A, hxA, hA⟩ := exists_open_preimage_pointClosureSmoothLocus k X x
  let U := A ⊓ V
  let i := pointClosureInclusion k X x
  let p := pointClosureStructure k X x
  let j := (i ⁻¹ᵁ U).ι
  have hs : Smooth (j ≫ p) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro y _
    rw [← hA]
    change i (j y) ∈ A
    exact (show i (j y) ∈ U from y.2).1
  refine ⟨U, ⟨hxA, hx⟩, inf_le_right, ?_⟩
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  exact hs

variable {k X x}
variable {U V : X.left.Opens}

omit [PerfectField k] in
/-- The actual smooth scheme structure on a smooth restriction of a point closure. -/
def smoothPointClosure
    (hU : Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom))) :
    SmoothSite (Spec (CommRingCat.of k)) :=
  letI := hU
  SmoothSite.mk ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom))

omit [PerfectField k] in
/-- The smooth restriction mapped into its actual ambient open. -/
def smoothPointClosureInclusion
    (hU : Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom))) :
    smoothPointClosure hU ⟶ (opensFunctor X).obj U :=
  homMk (pointClosureInclusion k X x ∣_ U) rfl

instance
    (hU : Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom))) :
    IsClosedImmersion (smoothPointClosureInclusion hU).left :=
  inferInstanceAs (IsClosedImmersion (pointClosureInclusion k X x ∣_ U))

omit [PerfectField k] in
/-- The original open inclusion between smooth restrictions of the reduced closure. -/
def smoothPointClosureMap
    (hU : Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom)))
    (hV : Smooth ((pointClosureInclusion k X x ∣_ V) ≫ (V.ι ≫ X.hom)))
    (h : U ≤ V) : smoothPointClosure hU ⟶ smoothPointClosure hV :=
  homMk ((pointClosure k X x).homOfLE ((pointClosureInclusion k X x).preimage_mono h)) (by
    change _ ≫ (pointClosureInclusion k X x ∣_ V) ≫ V.ι ≫ X.hom =
      (pointClosureInclusion k X x ∣_ U) ≫ U.ι ≫ X.hom
    simp only [morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc])

omit [PerfectField k] in
/-- The maps of the smooth restrictions retain the actual Cartesian square of closed pairs. -/
theorem smoothPointClosureMap_isPullback
    (hU : Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom)))
    (hV : Smooth ((pointClosureInclusion k X x ∣_ V) ≫ (V.ι ≫ X.hom)))
    (h : U ≤ V) :
    IsPullback (smoothPointClosureInclusion hU).left (smoothPointClosureMap hU hV h).left
      ((opensFunctor X).map (homOfLE h)).left (smoothPointClosureInclusion hV).left := by
  let i := pointClosureInclusion k X x
  change IsPullback (i ∣_ U) ((pointClosure k X x).homOfLE (i.preimage_mono h))
    (X.left.homOfLE h) (i ∣_ V)
  refine IsPullback.of_bot ?_ (morphismRestrict_homOfLE i U V h)
    (isPullback_morphismRestrict i V)
  simpa only [Scheme.homOfLE_ι] using isPullback_morphismRestrict i U

omit [PerfectField k] in
/-- Further ambient restrictions of a smooth reduced closure are smooth. -/
theorem smooth_pointClosure_of_le
    (hV : Smooth ((pointClosureInclusion k X x ∣_ V) ≫ (V.ι ≫ X.hom)))
    (h : U ≤ V) :
    Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom)) := by
  let i := pointClosureInclusion k X x
  let t := (pointClosure k X x).homOfLE (i.preimage_mono h)
  let := hV
  have ht : t ≫ ((i ∣_ V) ≫ (V.ι ≫ X.hom)) = (i ∣_ U) ≫ (U.ι ≫ X.hom) := by
    simp only [morphismRestrict_ι_assoc, t, Scheme.homOfLE_ι_assoc]
  rw [← ht]
  infer_instance

section Dimension

/-- Pure relative dimension is invariant under equality of the structure maps. -/
theorem relativeDimension_transport
    {S Y : Scheme.{u}} {f g : Y ⟶ S} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (h : f = g) {d : ℕ} (hf : RelativeDimension f d) : RelativeDimension g d := by
  subst g
  exact hf

omit [PerfectField k] in
private theorem localDim_of_relativeDimension
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    {d : ℕ} (h : RelativeDimension f d) (y : Y) :
    topologicalKrullDimAt Y y = (d : WithBot ℕ∞) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  let S := Spec (CommRingCat.of k)
  have hs : topologicalKrullDimAt S (f y) = 0 :=
    (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k S (𝟙 S) (f y)).symm.trans
      (topologicalKrullDim_eq_zero_of_subsingleton (Y := S))
  rw [topologicalKrullDimAt_eq_add_of_relativeDimension f h, hs, zero_add]

omit [PerfectField k] in
/-- A closed immersion of smooth schemes of pure dimensions `m` and `n`
sends the generic point of the source to a point of codimension `n - m`. -/
theorem codimension_generic_closedImmersion
    {Y T : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (i : T ⟶ Y) [IsClosedImmersion i] [Smooth (i ≫ f)]
    {n m : ℕ} (hn : RelativeDimension f n) (hm : RelativeDimension (i ≫ f) m)
    (t : T) (ht : IsGenericPoint t Set.univ) :
    Order.coheight (i t) = (n - m : ℕ) := by
  let : Algebra k (Y.residueField (i t)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation (i t)).hom.toAlgebra
  let : Algebra k (T.residueField t) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫ T.Γevaluation t).hom.toAlgebra
  have hY := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y f (i t)
  have hT := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k T (i ≫ f) t
  have htr := trdeg_residueField_of_surjectiveOnStalks k f i t
  let : IrreducibleSpace T := (irreducibleSpace_def T).2 ht.isIrreducible
  have hz := ringKrullDim_stalk_eq_zero_of_mem_genericPoints T t
    (mem_genericPoints_of_isGenericPoint_univ ht)
  rw [hz, add_zero] at hT
  rw [htr, ← hT, localDim_of_relativeDimension (k := k) (i ≫ f) hm, ringKrullDim_stalk_eq_coheight,
    localDim_of_relativeDimension (k := k) f hn] at hY
  have hd : (n : ℕ∞) = (m : ℕ∞) + Order.coheight (i t) :=
    WithBot.coe_injective (hY.trans (WithBot.coe_add _ _).symm)
  have hfin : Order.coheight (i t) ≠ ⊤ := fun he =>
    ENat.natCast_ne_top n (by simpa only [he, add_top] using hd)
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hp] at hd ⊢
  have : n = m + p := by exact_mod_cast hd
  exact congrArg (fun d : ℕ => (d : ℕ∞)) (by omega)

variable (k X x)

/-- In arbitrarily small ambient neighborhoods the reduced closure is smooth,
both schemes have pure relative dimension, and their dimension drop is the
codimension of the original point. -/
theorem exists_pure_smooth_pointClosure_restriction (V : X.left.Opens) (hx : x ∈ V) :
    ∃ (U : X.left.Opens) (_ : x ∈ U) (_ : U ≤ V)
      (hU : Smooth ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom))) (n m : ℕ),
      RelativeDimension (U.ι ≫ X.hom) n ∧
        RelativeDimension (smoothPointClosure hU).hom m ∧ Order.coheight x = (n - m : ℕ) := by
  obtain ⟨A, _, hcover, _, hdim⟩ :=
    exists_clopen_relativeDimension X.hom (isCohenMacaulay_fiber_of_smooth X.hom)
  have hxA : x ∈ iSup A := hcover ▸ trivial
  obtain ⟨n, hn⟩ := Opens.mem_iSup.mp hxA
  obtain ⟨U, hxU, hUV, hU⟩ :=
    exists_smooth_pointClosure_restriction k X x (V ⊓ A n) ⟨hx, hn⟩
  have hn' : RelativeDimension (U.ι ≫ X.hom) n := by
    let j := X.left.homOfLE (hUV.trans inf_le_right)
    have hj : j ≫ ((A n).ι ≫ X.hom) = U.ι ≫ X.hom := by
      simp only [j, Scheme.homOfLE_ι_assoc]
    exact relativeDimension_transport hj
      (RelativeDimension.comp_isOpenImmersion j _ (hdim n))
  let : Nonempty (pointClosureOpen k X x U).toScheme := pointClosureOpen_nonempty U hxU
  let := hU
  obtain ⟨m, hm⟩ := exists_relativeDimension_of_smooth_of_preconnectedSpace
    ((pointClosureInclusion k X x ∣_ U) ≫ (U.ι ≫ X.hom))
  have hcod := codimension_generic_closedImmersion (k := k) (U.ι ≫ X.hom)
    (pointClosureInclusion k X x ∣_ U) hn' hm _ (isGenericPoint_pointClosureGeneric U hxU)
  rw [pointClosureInclusion_restrict_generic U hxU] at hcod
  have hheight := coheight_eq_of_isOpenImmersion (x := (⟨x, hxU⟩ : U.toScheme)) U.ι
  rw [show U.ι (⟨x, hxU⟩ : U.toScheme) = x from U.ι_apply _] at hheight
  exact ⟨U, hxU, hUV.trans inf_le_left, hU, n, m, hn', hm, hheight.trans hcod⟩

end Dimension

end AlgebraicGeometry.SheafWithTransfers.Gersten
