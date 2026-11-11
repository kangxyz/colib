/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FaceSquare
public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointPushforward
public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext
public import Colib.AlgebraicGeometry.Correspondences.Singular.Maps
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FreeModule.PID
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree

/-!
# Finite cycle corestriction commutes with the actual diagonal faces

For an admissible prime, the graph coface is the whole original fiber with
its generic stalk lengths. The coefficient-change square transports both
fibers to the same polynomial endpoint. The finite component restriction
then pushes the full endpoint cycle with its actual generic residue degree.
Additivity extends the identity to all signed unreduced correspondences.

Adapted from Motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/WeightTwo/CorestrictionBoundary.lean:228-353`, and
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/FiniteFlat/Components.lean:37-73`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped Polynomial Simplicial

attribute [local instance] Stacks.Chow.isIntegral_integralComponentAt

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFiniteCyclePushforward

open _root_.AlgebraicGeometry.Scheme PolynomialEndpointFiber

/-- A finite integral support surjecting onto the polynomial line is flat. -/
theorem flat_finite_surjective_polynomial {k : Type u} [Field k]
    {C : Scheme.{u}} [IsIntegral C] (g : C ⟶ Spec (.of k[X])) [IsFinite g] [Surjective g] :
    Flat g := by
  let : IsAffine C := isAffine_of_isAffineHom g
  let e : Γ(Spec (.of k[X]), ⊤) ≃+* k[X] :=
    (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv
  let φ : k[X] →+* Γ(C, ⊤) := g.appTop.hom.comp e.symm.toRingHom
  let : Algebra k[X] Γ(C, ⊤) := φ.toAlgebra
  let : Module.Finite k[X] Γ(C, ⊤) := by
    change φ.Finite
    exact g.finite_appTop.comp (RingHom.Finite.of_surjective _ e.symm.surjective)
  let : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isDominant g
  have hg : Function.Injective g.appTop.hom := g.app_injective ⊤
  let : Module.IsTorsionFree k[X] Γ(C, ⊤) := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    exact hg.comp e.symm.injective
  let : Module.Free k[X] Γ(C, ⊤) := Module.free_of_finite_type_torsion_free'
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  have hflat : φ.Flat := by
    change Module.Flat k[X] Γ(C, ⊤)
    infer_instance
  have he : g.appTop.hom = φ.comp e.toRingHom := by
    ext r
    simp [φ]
  rw [he]
  exact (RingHom.Flat.of_bijective e.bijective).comp hflat

private abbrev supportProjection (F : Type u) [Field F] (q : ℕ) (z : ambient F 1 q) :
    (integralComponentAt z).subscheme ⟶ (source F 1).left :=
  (integralComponentAt z).subschemeι ≫ pullback.fst (source F 1).hom (target F q).hom

private theorem supportProjection_surjective (F : Type u) [Field F] (q : ℕ)
    (z : ambient F 1 q) (hz : IsFiniteCorrespondencePoint (source F 1).hom (target F q).hom z) :
    Surjective (supportProjection F q z) := by
  have h : Set.range (supportProjection F q z) ∈ irreducibleComponents (source F 1).left := hz.2
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
  exact ⟨Set.range_eq_univ.mp h⟩

private theorem supportProjection_flat (F : Type u) [Field F] (q : ℕ)
    (z : ambient F 1 q) (hz : IsFiniteCorrespondencePoint (source F 1).hom (target F q).hom z) :
    Flat (supportProjection F q z) := by
  let : IsFinite (supportProjection F q z) := hz.1
  let : Surjective (supportProjection F q z) := supportProjection_surjective F q z hz
  let : Flat (supportProjection F q z ≫ (sourceChart1 F).hom) :=
    flat_finite_surjective_polynomial _
  have h : supportProjection F q z =
      (supportProjection F q z ≫ (sourceChart1 F).hom) ≫ (sourceChart1 F).inv := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

private theorem finiteCyclePushforward_congr_hom {A B : Scheme.{u}}
    (r s : A ⟶ B) [IsFinite r] [IsFinite s] (h : r = s) (c : AlgebraicCycle A ℤ) :
    finiteCyclePushforward r c = finiteCyclePushforward s c := by
  cases h
  rfl

private theorem graphFace_push_ambient_of_iso (F : Type u) [Field F] (q : ℕ)
    (z : ambient F 1 q) (hz : IsFiniteCorrespondencePoint (source F 1).hom (target F q).hom z)
    (i : Fin 2) {D : Scheme.{u}} [IsNoetherian D]
    (j : D ⟶ (integralComponentAt z).subscheme) [IsFinite j]
    (e : pullback (sourceFace F i).left (supportProjection F q z) ≅ D)
    (he : e.hom ≫ j = pullback.snd (sourceFace F i).left (supportProjection F q z)) :
    finiteCyclePushforward (ambientFace F q i)
      (((Cor.graphFunctor F).map (sourceFace F i)) ≫
        singleFiniteCorrespondence (source F 1).hom (target F q).hom z hz 1).val =
      finiteCyclePushforward (j ≫ (integralComponentAt z).subschemeι)
        (AlgebraicCycle.fundamentalCycle D) := by
  let : Flat (supportProjection F q z) := supportProjection_flat F q z hz
  let : IsNoetherian (source F 0).left :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of F)) (source F 0).hom
      toCompactSpace :=
        QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of F)) (source F 0).hom }
  let : IsNoetherian (pullback (sourceFace F i).left (supportProjection F q z)) :=
    isNoetherian_correspondenceGraphFiber (source F 1).hom (target F q).hom z
      (sourceFace F i).left hz
  let m := correspondenceGraphFiberMap (source F 0).hom (source F 1).hom (target F q).hom z
    (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i))
  have hm : m ≫ ambientFace F q i = e.hom ≫ (j ≫ (integralComponentAt z).subschemeι) := by
    calc
      _ = pullback.snd (sourceFace F i).left (supportProjection F q z) ≫
            (integralComponentAt z).subschemeι := graphFiberMap_ambientFace F q z i
      _ = _ := by rw [← he, Category.assoc]
  rw [Cor.graph_comp_single_val_eq_fiber (X := source F 0) (Y := source F 1)
      (Z := target F q) F z hz (sourceFace F i), finiteCyclePushforward_comp_apply]
  calc
    _ = finiteCyclePushforward (e.hom ≫ (j ≫ (integralComponentAt z).subschemeι))
        (AlgebraicCycle.fundamentalCycle
          (pullback (sourceFace F i).left (supportProjection F q z))) :=
      finiteCyclePushforward_congr_hom _ _ hm _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso]

section ScalarChange

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The graph face of a coefficient-one prime transfers with its actual ambient residue degree. -/
theorem finitePushforward_face_single_val (q : ℕ) (i : Fin 2) (z : ambient E 1 q)
    (hz : IsFiniteCorrespondencePoint (source E 1).hom (target E q).hom z) :
    finiteCyclePushforward (ambientMap (k := k) (E := E) 0 q)
      (((Cor.graphFunctor E).map (sourceFace E i)) ≫
        singleFiniteCorrespondence (source E 1).hom (target E q).hom z hz 1).val =
    ((ambientMap (k := k) (E := E) 1 q).residueDegree z : ℤ) •
      (((Cor.graphFunctor k).map (sourceFace k i)) ≫
        singleFiniteCorrespondence (source k 1).hom (target k q).hom
          (ambientMap (k := k) (E := E) 1 q z)
          (imagePoint_admissible (k := k) 1 q z hz) 1).val := by
  let m := ambientMap (k := k) (E := E) 1 q
  let : IsFinite m := ambientMap_isFinite (k := k) (E := E) 1 q
  let y := m z
  have hy : IsFiniteCorrespondencePoint (source k 1).hom (target k q).hom y :=
    imagePoint_admissible (k := k) 1 q z hz
  let j : (integralComponentAt z).subscheme ⟶ (integralComponentAt y).subscheme :=
    integralComponentMap m z
  let l := (integralComponentAt z).subschemeι
  let r := (integralComponentAt y).subschemeι
  let : IsClosedImmersion l :=
    inferInstanceAs (IsClosedImmersion (integralComponentAt z).subschemeι)
  let : IsClosedImmersion r :=
    inferInstanceAs (IsClosedImmersion (integralComponentAt y).subschemeι)
  have hj : j ≫ r = l ≫ m := integralComponentMap_subschemeι m z
  let : IsFinite (j ≫ r) := by rw [hj]; infer_instance
  let : IsFinite j := IsFinite.of_comp j r
  let : IsDominant j := inferInstanceAs (IsDominant (integralComponentMap m z))
  let : IsFinite (supportProjection E q z) := hz.1
  let : IsFinite (supportProjection k q y) := hy.1
  let : Surjective (supportProjection E q z) := supportProjection_surjective E q z hz
  let : Surjective (supportProjection k q y) := supportProjection_surjective k q y hy
  let f := (supportProjection E q z ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom
  let g := supportProjection k q y ≫ (sourceChart1 k).hom
  let : IsFinite f := inferInstanceAs (IsFinite
    ((supportProjection E q z ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom))
  let : IsFinite g := inferInstanceAs (IsFinite (supportProjection k q y ≫ (sourceChart1 k).hom))
  let : Surjective f := inferInstanceAs (Surjective
    ((supportProjection E q z ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom))
  let : Surjective g := inferInstanceAs
    (Surjective (supportProjection k q y ≫ (sourceChart1 k).hom))
  let : Flat f := flat_finite_surjective_polynomial f
  let : Flat g := flat_finite_surjective_polynomial g
  have hparam : j ≫ g = f := by
    change j ≫ (supportProjection k q y ≫ (sourceChart1 k).hom) = _
    rw [← Category.assoc]
    exact congrArg (fun t => t ≫ (sourceChart1 k).hom)
      (integralComponentMap_sourceProjection (k := k) (E := E) q z)
  let a : k := i.val
  let : IsNoetherian (fiber f a) := fiber_isNoetherian f a
  let : IsNoetherian (fiber g a) := fiber_isNoetherian g a
  have hE := graphFace_push_ambient_of_iso E q z hz i (fiberInclusion f a)
    (scalarFaceEndpointIso (k := k) (supportProjection E q z) i)
    (scalarFaceEndpointIso_hom_inclusion (k := k) (supportProjection E q z) i)
  have hk := graphFace_push_ambient_of_iso k q y hy i (fiberInclusion g a)
    (faceEndpointIso k (supportProjection k q y) i)
    (faceEndpointIso_hom_inclusion k (supportProjection k q y) i)
  have hcycle : finiteCyclePushforward (fiberInclusion f a ≫ j)
        (AlgebraicCycle.fundamentalCycle (fiber f a)) =
      (m.residueDegree z : ℤ) • finiteCyclePushforward (fiberInclusion g a)
        (AlgebraicCycle.fundamentalCycle (fiber g a)) := by
    have h := finiteCyclePushforward_fundamentalCycle_comp f g j hparam a
    have hd := finrank_functionField_integralComponent m z
    dsimp only at h hd
    rw [hd] at h
    exact h
  have hmove (c : AlgebraicCycle (ambient E 0 q) ℤ) :
      finiteCyclePushforward (ambientFace k q i)
          (finiteCyclePushforward (ambientMap (k := k) (E := E) 0 q) c) =
        finiteCyclePushforward m (finiteCyclePushforward (ambientFace E q i) c) := by
    rw [finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply]
    exact finiteCyclePushforward_congr_hom _ _ (ambientMap_face (k := k) (E := E) q i).symm c
  apply finiteCyclePushforward_injective_of_isClosedImmersion (ambientFace k q i)
  rw [hmove, map_zsmul, hE, hk, finiteCyclePushforward_comp_apply]
  have hmap : (fiberInclusion f a ≫ l) ≫ m = (fiberInclusion f a ≫ j) ≫ r := by
    simp only [Category.assoc, hj]
  calc
    _ = finiteCyclePushforward ((fiberInclusion f a ≫ j) ≫ r)
        (AlgebraicCycle.fundamentalCycle (fiber f a)) :=
      finiteCyclePushforward_congr_hom _ _ hmap _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply (fiberInclusion f a ≫ j) r,
        hcycle, map_zsmul, finiteCyclePushforward_comp_apply]

/-- Finite corestriction commutes with both original unreduced cofaces on every signed cycle. -/
theorem cyclePushforward_face (q : ℕ) (i : Fin 2)
    (α : Cor.mk (source E 1) ⟶ Cor.mk (target E q)) :
    cyclePushforward (k := k) (E := E) 0 q
      ((Cor.simplexProductCosimplicial (Cor.mk (SmoothSite.base (Spec (.of E))))).δ i ≫ α) =
    (Cor.simplexProductCosimplicial (Cor.mk (SmoothSite.base (Spec (.of k))))).δ i ≫
      cyclePushforward (k := k) (E := E) 1 q α := by
  let dE := (Cor.graphFunctor E).map (sourceFace E i)
  let dk := (Cor.graphFunctor k).map (sourceFace k i)
  have h : (cyclePushforward (k := k) (E := E) 0 q).comp
      (Preadditive.leftComp (Cor.mk (target E q)) dE) =
    (Preadditive.leftComp (Cor.mk (target k q)) dk).comp
      (cyclePushforward (k := k) (E := E) 1 q) := by
    apply finiteCorrespondences.addHom_ext_one (source E 1).hom (target E q).hom
    intro z hz
    change cyclePushforward (k := k) (E := E) 0 q
        (dE ≫ singleFiniteCorrespondence (source E 1).hom (target E q).hom z hz 1) =
      dk ≫ cyclePushforward (k := k) (E := E) 1 q
        (singleFiniteCorrespondence (source E 1).hom (target E q).hom z hz 1)
    rw [cyclePushforward_single, one_mul,
      singleFiniteCorrespondence_eq_zsmul (source k 1).hom (target k q).hom,
      Preadditive.comp_zsmul]
    apply Subtype.ext
    rw [cyclePushforward_val]
    exact finitePushforward_face_single_val (k := k) (E := E) q i z hz
  change cyclePushforward (k := k) (E := E) 0 q (dE ≫ α) =
    dk ≫ cyclePushforward (k := k) (E := E) 1 q α
  exact DFunLike.congr_fun h α

end ScalarChange

end AlgebraicGeometry.MotivicCohomology.DiagonalFiniteCyclePushforward
