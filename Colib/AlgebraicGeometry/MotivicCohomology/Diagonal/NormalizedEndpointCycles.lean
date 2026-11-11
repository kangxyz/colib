/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.BoundarySupports
public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.SpecOrder

/-!
# Full normalized endpoint cycles of native diagonal supports

The canonical finite normalization has the same function field as the
original support. The degree-one endpoint pushforward therefore retains the
full native fundamental cycle. Both projections and the torus coordinates
are those of the original graph fiber.

Adapted from Motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Diagonal/BoundaryFibers.lean:67-137` and
`Motivic/Cohomology/Diagonal/NormalizedEndpointCycles.lean:38-158`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped Polynomial nonZeroDivisors

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalBoundarySupport

open _root_.AlgebraicGeometry.Scheme DiagonalFiniteCyclePushforward PolynomialEndpointFiber

variable {k : Type u} [Field k] {q : ℕ} (Z : Generator k q)

theorem normalizationMap_appTop :
    (normalizationMap Z).appTop =
      CommRingCat.ofHom (algebraMap (coordinateRing Z) (normalizationRing Z)) ≫
        (Scheme.ΓSpecIso (.of (normalizationRing Z))).inv := by
  have hi : (supportIsoSpec Z).inv.appTop = (Scheme.ΓSpecIso (coordinateRing Z)).inv := by
    apply (cancel_mono (Scheme.ΓSpecIso (coordinateRing Z)).hom).mp
    rw [Iso.inv_hom_id]
    have hΓ : (supportIsoSpec Z).hom.appTop = (Scheme.ΓSpecIso (coordinateRing Z)).hom :=
      Scheme.toSpecΓ_appTop (support Z)
    rw [← hΓ, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [normalizationMap, Scheme.Hom.comp_appTop, hi]
  exact (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (coordinateRing Z) (normalizationRing Z)))).symm

/-- The actual normalization induces a degree-one extension on function fields. -/
theorem normalizationMap_finrank :
    letI : Algebra (support Z).functionField (Spec (.of (normalizationRing Z))).functionField :=
      (dominantFunctionFieldMap (normalizationMap Z)).toAlgebra
    Module.finrank (support Z).functionField
      (Spec (.of (normalizationRing Z))).functionField = 1 := by
  let C := support Z
  let N := normalizationRing Z
  let D := Spec (.of N)
  let B := coordinateRing Z
  let K := FractionRing B
  let j := normalizationMap Z
  let : IsDominant j := inferInstanceAs (IsDominant (normalizationMap Z))
  let : Nonempty ((⊤ : C.Opens) : Type u) := ⟨⟨genericPoint C, trivial⟩⟩
  let : Nonempty ((⊤ : D.Opens) : Type u) := ⟨⟨genericPoint D, trivial⟩⟩
  let : IsFractionRing B C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C ⊤ (isAffineOpen_top C)
  let : IsDomain (CommRingCat.of N) := inferInstanceAs (IsDomain N)
  let : Algebra (CommRingCat.of N) K := inferInstanceAs (Algebra N K)
  let : IsFractionRing (CommRingCat.of N) K := normalizationFractionRing Z
  let eC := IsLocalization.algEquiv (nonZeroDivisors B) C.functionField K
  let eD := specFunctionFieldEquiv (CommRingCat.of N) K
  have hj (b : B) : dominantFunctionFieldMap j (algebraMap B C.functionField b) =
      specAlgebraMap (CommRingCat.of N) (algebraMap B N b) := by
    have h := DFunLike.congr_fun (Stacks.Chow.appLE_germToFunctionField_commutes j ⊤ ⊤ le_top) b
    have happ : j.appLE ⊤ ⊤ le_top = (normalizationMap Z).appTop :=
      Scheme.Hom.appLE_eq_app j (U := ⊤)
    rw [happ, normalizationMap_appTop] at h
    change D.germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of N)).inv (algebraMap B N b)) =
      dominantFunctionFieldMap j (algebraMap B C.functionField b) at h
    rw [germToFunctionField_eq_specAlgebraMap] at h
    exact h.symm
  have hcomp : eD.toRingHom.comp (dominantFunctionFieldMap j) =
      eC.toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext b
    change eD (dominantFunctionFieldMap j (algebraMap B C.functionField b)) =
      eC (algebraMap B C.functionField b)
    rw [hj]
    change specFunctionFieldEquiv (CommRingCat.of N) K
        (specAlgebraMap (CommRingCat.of N) (algebraMap B N b)) = _
    rw [specFunctionFieldEquiv_specAlgebraMap, eC.commutes, ← IsScalarTower.algebraMap_apply B N K]
  have hbij : Function.Bijective (dominantFunctionFieldMap j) := by
    refine ⟨(dominantFunctionFieldMap j).injective, ?_⟩
    intro x
    refine ⟨eC.symm (eD x), eD.injective ?_⟩
    have h := DFunLike.congr_fun hcomp (eC.symm (eD x))
    change eD (dominantFunctionFieldMap j (eC.symm (eD x))) = eC (eC.symm (eD x)) at h
    rwa [eC.apply_symm_apply] at h
  let : Algebra C.functionField D.functionField := (dominantFunctionFieldMap j).toAlgebra
  let e := AlgEquiv.ofBijective (Algebra.ofId C.functionField D.functionField) hbij
  change Module.finrank C.functionField D.functionField = 1
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The native graph fiber of the original affine evaluation point. -/
abbrev graphFiber (a : k) :=
  correspondenceGraphFiber (source k 1).hom (target k q).hom Z.val (evaluationPoint k a).left

/-- The graph fiber's finite map to the original point-to-torus ambient. -/
abbrev graphFiberInclusion (a : k) :=
  correspondenceGraphFiberMap (SmoothSite.base (Spec (.of k))).hom (source k 1).hom
    (target k q).hom Z.val (evaluationPoint k a).left
    (MorphismProperty.Over.w (evaluationPoint k a))

theorem graphFiber_isPullback (a : k) :
    IsPullback (pullback.fst (evaluationPoint k a).left (projection Z))
      (pullback.snd (evaluationPoint k a).left (projection Z))
      (endpoint a) (polynomialProjection Z) :=
  (IsPullback.of_hasPullback (evaluationPoint k a).left (projection Z)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (sourceChart1 k)
    (by simp) (by simp) (by simpa only [Iso.refl_hom, Category.id_comp]
      using evaluationPoint_chart k a) (by simp)

/-- The whole graph fiber in the literal polynomial endpoint chart. -/
def graphFiberIso (a : k) : graphFiber Z a ≅ fiber (polynomialProjection Z) a :=
  (graphFiber_isPullback Z a).isoPullback

@[reassoc] theorem graphFiberIso_inv_support (a : k) :
    (graphFiberIso Z a).inv ≫ pullback.snd (evaluationPoint k a).left (projection Z) =
      fiberInclusion (polynomialProjection Z) a := by
  rw [← (graphFiber_isPullback Z a).isoPullback_hom_snd]
  exact Iso.inv_hom_id_assoc _ _

@[reassoc] theorem graphFiberIso_inv_point (a : k) :
    (graphFiberIso Z a).inv ≫ pullback.fst (evaluationPoint k a).left (projection Z) =
      pullback.fst (endpoint a) (polynomialProjection Z) := by
  rw [← (graphFiber_isPullback Z a).isoPullback_hom_fst]
  exact Iso.inv_hom_id_assoc _ _

/-- The entire fiber of the actual normalization over the original polynomial endpoint. -/
abbrev normalizedFiber (a : k) := fiber (normalizationBaseMap Z) a

/-- The original field projection of the whole normalized endpoint. -/
abbrev normalizedFiberBase (a : k) : normalizedFiber Z a ⟶ Spec (.of k) :=
  pullback.fst (endpoint a) (normalizationBaseMap Z)

instance normalizedFiberBaseFinite [CharZero k] (a : k) : IsFinite (normalizedFiberBase Z a) :=
  inferInstanceAs (IsFinite (pullback.fst (endpoint a) (normalizationBaseMap Z)))

instance normalizedFiberNoetherian [CharZero k] (a : k) : IsNoetherian (normalizedFiber Z a) :=
  fiber_isNoetherian (normalizationBaseMap Z) a

/-- The actual restriction of the normalization morphism to the original polynomial endpoint. -/
def normalizedPolynomialFiberMap (a : k) : normalizedFiber Z a ⟶ fiber (polynomialProjection Z) a :=
  pullback.lift (normalizedFiberBase Z a)
    (fiberInclusion (normalizationBaseMap Z) a ≫ normalizationMap Z) (by
      rw [Category.assoc, normalizationMap_polynomialProjection]
      exact pullback.condition)

@[reassoc] theorem normalizedPolynomialFiberMap_support (a : k) :
    normalizedPolynomialFiberMap Z a ≫ fiberInclusion (polynomialProjection Z) a =
      fiberInclusion (normalizationBaseMap Z) a ≫ normalizationMap Z :=
  pullback.lift_snd _ _ _

@[reassoc] theorem normalizedPolynomialFiberMap_point (a : k) :
    normalizedPolynomialFiberMap Z a ≫ pullback.fst (endpoint a) (polynomialProjection Z) =
      normalizedFiberBase Z a :=
  pullback.lift_fst _ _ _

theorem normalizedPolynomialFiberMap_isPullback (a : k) :
    IsPullback (normalizedPolynomialFiberMap Z a) (fiberInclusion (normalizationBaseMap Z) a)
      (fiberInclusion (polynomialProjection Z) a) (normalizationMap Z) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst (endpoint a) (polynomialProjection Z))
    (h₂₂ := polynomialProjection Z) (v₁₃ := endpoint a)
  · rw [normalizedPolynomialFiberMap_point, normalizationMap_polynomialProjection]
    exact IsPullback.of_hasPullback (endpoint a) (normalizationBaseMap Z)
  · exact normalizedPolynomialFiberMap_support Z a
  · exact IsPullback.of_hasPullback (endpoint a) (polynomialProjection Z)

instance normalizedPolynomialFiberMapFinite [CharZero k] (a : k) :
    IsFinite (normalizedPolynomialFiberMap Z a) :=
  MorphismProperty.of_isPullback (normalizedPolynomialFiberMap_isPullback Z a).flip
    (inferInstance : IsFinite (normalizationMap Z))

/-- The normalized endpoint maps to the original graph fiber through its whole affine chart. -/
def normalizedFiberMap (a : k) : normalizedFiber Z a ⟶ graphFiber Z a :=
  normalizedPolynomialFiberMap Z a ≫ (graphFiberIso Z a).inv

instance normalizedFiberMapFinite [CharZero k] (a : k) : IsFinite (normalizedFiberMap Z a) :=
  inferInstanceAs (IsFinite (normalizedPolynomialFiberMap Z a ≫ (graphFiberIso Z a).inv))

/-- The actual normalized endpoint map into the original point-to-torus ambient. -/
def normalizedFiberInclusion (a : k) := normalizedFiberMap Z a ≫ graphFiberInclusion Z a

instance normalizedFiberInclusionFinite [CharZero k] (a : k) :
    IsFinite (normalizedFiberInclusion Z a) :=
  inferInstanceAs (IsFinite (normalizedFiberMap Z a ≫ graphFiberInclusion Z a))

@[reassoc] theorem normalizedFiberInclusion_fst (a : k) :
    normalizedFiberInclusion Z a ≫ pullback.fst _ _ = normalizedFiberBase Z a := by
  rw [normalizedFiberInclusion, Category.assoc, correspondenceGraphFiberMap_fst,
    normalizedFiberMap, Category.assoc, graphFiberIso_inv_point, normalizedPolynomialFiberMap_point]

@[reassoc] theorem normalizedFiberInclusion_snd (a : k) :
    normalizedFiberInclusion Z a ≫ pullback.snd _ _ =
      fiberInclusion (normalizationBaseMap Z) a ≫ normalizationMap Z ≫ targetProjection Z := by
  rw [normalizedFiberInclusion, Category.assoc, correspondenceGraphFiberMap_snd,
    normalizedFiberMap, Category.assoc, graphFiberIso_inv_support_assoc,
    normalizedPolynomialFiberMap_support_assoc]

/-- The original normalization scalar map on the whole endpoint's global functions. -/
def normalizedFiberScalar (a : k) : normalizationRing Z →+* Γ(normalizedFiber Z a, ⊤) :=
  (fiberInclusion (normalizationBaseMap Z) a).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (normalizationRing Z))).inv.hom

variable [CharZero k]

private theorem finiteCyclePushforward_congr_hom {A B : Scheme.{u}}
    (f g : A ⟶ B) [IsFinite f] [IsFinite g] (h : f = g) (c : AlgebraicCycle A ℤ) :
    finiteCyclePushforward f c = finiteCyclePushforward g c := by
  cases h
  rfl

/-- Finite normalization preserves the entire original polynomial endpoint cycle. -/
theorem normalizedPolynomialFiberMap_fundamentalCycle (a : k) :
    letI : IsNoetherian (fiber (polynomialProjection Z) a) :=
      fiber_isNoetherian (polynomialProjection Z) a
    finiteCyclePushforward (normalizedPolynomialFiberMap Z a)
        (AlgebraicCycle.fundamentalCycle (normalizedFiber Z a)) =
      AlgebraicCycle.fundamentalCycle (fiber (polynomialProjection Z) a) := by
  let : IsNoetherian (fiber (polynomialProjection Z) a) :=
    fiber_isNoetherian (polynomialProjection Z) a
  have h := finiteCyclePushforward_fundamentalCycle_comp (normalizationBaseMap Z)
    (polynomialProjection Z) (normalizationMap Z) (normalizationMap_polynomialProjection Z) a
  rw [normalizationMap_finrank Z, Nat.cast_one, one_zsmul] at h
  apply finiteCyclePushforward_injective_of_isClosedImmersion
    (fiberInclusion (polynomialProjection Z) a)
  rw [finiteCyclePushforward_comp_apply]
  exact (finiteCyclePushforward_congr_hom _ _ (normalizedPolynomialFiberMap_support Z a) _).trans h

omit [CharZero k] in
/-- The original graph fiber of the finite support is Noetherian. -/
theorem graphFiberNoetherian (a : k) : IsNoetherian (graphFiber Z a) := by
  let : IsNoetherian (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsNoetherian (Spec (.of k)))
  exact isNoetherian_correspondenceGraphFiber (source k 1).hom (target k q).hom Z.val
    (evaluationPoint k a).left Z.property

/-- The actual normalized fiber map pushes its whole cycle to the graph fiber. -/
theorem normalizedFiberMap_fundamentalCycle (a : k) :
    letI : IsNoetherian (graphFiber Z a) := graphFiberNoetherian Z a
    finiteCyclePushforward (normalizedFiberMap Z a)
        (AlgebraicCycle.fundamentalCycle (normalizedFiber Z a)) =
      AlgebraicCycle.fundamentalCycle (graphFiber Z a) := by
  let : IsNoetherian (graphFiber Z a) := graphFiberNoetherian Z a
  let : IsNoetherian (fiber (polynomialProjection Z) a) :=
    fiber_isNoetherian (polynomialProjection Z) a
  change finiteCyclePushforward (normalizedPolynomialFiberMap Z a ≫ (graphFiberIso Z a).inv)
      (AlgebraicCycle.fundamentalCycle (normalizedFiber Z a)) =
    AlgebraicCycle.fundamentalCycle (graphFiber Z a)
  rw [← finiteCyclePushforward_comp_apply, normalizedPolynomialFiberMap_fundamentalCycle]
  exact finiteCyclePushforward_fundamentalCycle_iso (graphFiberIso Z a).symm

/-- The graph-composed endpoint cycle is computed on the full normalized polynomial fiber. -/
theorem graphEndpoint_val_eq_normalized (a : k) :
    ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
      singleFiniteCorrespondence (source k 1).hom (target k q).hom Z.val Z.property 1).val =
      finiteCyclePushforward (normalizedFiberInclusion Z a)
        (AlgebraicCycle.fundamentalCycle (normalizedFiber Z a)) := by
  let : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  let : IsNoetherian (graphFiber Z a) := graphFiberNoetherian Z a
  rw [Cor.graph_comp_single_val_eq_fiber (X := SmoothSite.base (Spec (.of k)))
    (Y := source k 1) (Z := target k q) k Z.val Z.property (evaluationPoint k a)]
  change finiteCyclePushforward (graphFiberInclusion Z a)
      (AlgebraicCycle.fundamentalCycle (graphFiber Z a)) =
    finiteCyclePushforward (normalizedFiberMap Z a ≫ graphFiberInclusion Z a)
      (AlgebraicCycle.fundamentalCycle (normalizedFiber Z a))
  rw [← finiteCyclePushforward_comp_apply, normalizedFiberMap_fundamentalCycle]

end AlgebraicGeometry.MotivicCohomology.DiagonalBoundarySupport
