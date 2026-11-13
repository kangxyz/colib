/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderEndpointMono
public import Colib.CategoryTheory.Sites.Simplicial.FiberCylinderHomotopy
public import Colib.CategoryTheory.Sites.Simplicial.MonoFactorization
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceRetract
import Colib.Topology.Realization.HomotopyBridge

/-!
# Lifting against all monomorphisms

Such a map admits a section and a homotopy from the section-retraction
composite to the identity. The original maps on each fiber are therefore
weak equivalences. Conversely, the factorization through a monomorphism
identifies weak injective fibrations with these lifting maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C)

/-- Right lifting against all monomorphisms gives an actual stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_of_mono_rlp
    {X Y : PointedSimplicialPresheaf.{w} C} {p : X ⟶ Y}
    (hp : (monomorphisms (PointedSimplicialPresheaf.{w} C)).rlp p) :
    stalkwiseWeakEquivalences C J p := by
  let s₀ := fromPoint C Y
  have hs₀ : Mono s₀ := mono_of_mono_fac
    ((point_isZero.{w} C).isInitial.hom_ext (s₀ ≫ toPoint C Y) (𝟙 _))
  let sq : CommSq (fromPoint C X) s₀ p (𝟙 Y) := ⟨
    (point_isZero.{w} C).isInitial.hom_ext _ _⟩
  let : HasLiftingProperty s₀ p := hp s₀ hs₀
  let s := sq.lift
  have hs : s ≫ p = 𝟙 Y := sq.fac_right
  let q := simplicialEndpointPair X
  let t := coprod.desc (p ≫ s) (𝟙 X)
  let q' : CommSq t q p (cylinderProjection X (interval C) ≫ p) := ⟨by
    apply coprod.hom_ext
    · simp only [t, q, simplicialEndpointPair, coprod.inl_desc_assoc, Category.assoc,
        cylinderSection_projection_assoc, hs, Category.comp_id]
    · simp only [t, q, simplicialEndpointPair, coprod.inr_desc_assoc,
        cylinderSection_projection_assoc, Category.id_comp]⟩
  let : HasLiftingProperty q p := hp q (mono_simplicialEndpointPair X)
  have h : CylinderHomotopic (p ≫ s) (𝟙 X) := by
    refine ⟨q'.lift, ?_, ?_⟩
    · simpa only [q, t, simplicialEndpointPair, coprod.inl_desc_assoc, coprod.inl_desc] using
        congrArg (coprod.inl ≫ ·) q'.fac_left
    · simpa only [q, t, simplicialEndpointPair, coprod.inr_desc_assoc, coprod.inr_desc] using
        congrArg (coprod.inr ≫ ·) q'.fac_left
  intro Φ
  let F := fiberAtPoint C Φ
  obtain ⟨H⟩ := nonempty_fiberSimplicialHomotopy_of_cylinderHomotopic Φ h
  let e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj (F.obj X)) (SSet.toTop.obj (F.obj Y)) := {
    toFun := (SSet.toTop.map (F.map p)).hom
    invFun := (SSet.toTop.map (F.map s)).hom
    left_inv := by
      have h' := (SSet.realizationSimplicialHomotopy H).symm
      rw [F.map_comp, F.map_id, Functor.map_comp, Functor.map_id,
        TopCat.hom_comp, TopCat.hom_id] at h'
      exact ⟨h'⟩
    right_inv := by
      have hs' : F.map s ≫ F.map p = 𝟙 _ := by rw [← F.map_comp, hs, F.map_id]
      have he := congrArg TopCat.Hom.hom (congrArg SSet.toTop.map hs')
      rw [Functor.map_comp, Functor.map_id, TopCat.hom_comp, TopCat.hom_id] at he
      rw [he] }
  exact Topology.isWeakHomotopyEquivalence_of_homotopyEquiv e

instance stalkwiseWeakEquivalences_isStableUnderRetracts :
    (stalkwiseWeakEquivalences.{w} C J).IsStableUnderRetracts where
  of_retract r h Φ :=
    Topology.IsWeakHomotopyEquivalence.of_retract (r.map (fiberAtPoint C Φ ⋙ SSet.toTop)) (h Φ)

omit [LocallySmall.{w} C] in
/-- A weak map with the injective right lifting property lifts against every
monomorphism. The factorization gives an actual retract of the right map. -/
theorem mono_rlp_of_weak_of_stalkwiseTrivial_rlp
    {X Y : PointedSimplicialPresheaf.{max u v} C} {p : X ⟶ Y}
    (hp : stalkwiseWeakEquivalences C J p) (hpf : (stalkwiseTrivialMonomorphisms C J).rlp p) :
    (monomorphisms (PointedSimplicialPresheaf.{max u v} C)).rlp p := by
  let W := monomorphisms (PointedSimplicialPresheaf.{max u v} C)
  let : HasFactorization W W.rlp := hasFactorization_monomorphisms_rlp C
  let : LocallySmall.{max u v} C := CategoryTheory.locallySmall_max
  let d := factorizationData W W.rlp p
  have hb := stalkwiseWeakEquivalences_of_mono_rlp C J d.hp
  have ha : stalkwiseTrivialMonomorphisms C J d.i :=
    ⟨d.hi, (stalkwiseWeakEquivalences C J).of_postcomp d.i d.p hb (d.fac.symm ▸ hp)⟩
  let sq : CommSq (𝟙 X) d.i p d.p := ⟨(Category.id_comp p).trans d.fac.symm⟩
  let : HasLiftingProperty d.i p := hpf d.i ha
  let r : RetractArrow p d.p :=
    ⟨Arrow.homMk d.i (𝟙 Y) (by
        change d.i ≫ d.p = p ≫ 𝟙 Y
        exact d.fac.trans (Category.comp_id _).symm),
      Arrow.homMk sq.lift (𝟙 Y) (by
        change sq.lift ≫ p = d.p ≫ 𝟙 Y
        exact sq.fac_right.trans (Category.comp_id _).symm), by
        apply Arrow.hom_ext
        · exact sq.fac_left
        · exact Category.id_comp _⟩
  exact W.rlp.of_retract r d.hp

end CategoryTheory.PointedSimplicialPresheaf
