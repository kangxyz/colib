/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointCycle

/-! # Endpoint precomposition for supported cycles on a closed subscheme -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber
open _root_.AlgebraicGeometry.AlgebraicCycle

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} [IsNoetherian D]
  (φ : X ⟶ Y) (q : Y.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
  (H : IsPullback φ.left X.hom q (point a))
  (m : D ⟶ pullback Y.hom Z.hom) [IsClosedImmersion m]

/-- An actual endpoint graph composes with each admissible signed prime by
taking the whole scalar fiber of its original closed support. -/
theorem graph_comp_closedCycle_endpoint (c : AlgebraicCycle D ℤ)
    (α : Cor.mk Y ⟶ Cor.mk Z) (hα : α.val = finiteCyclePushforward m c) :
    ((graphFunctor k).map φ ≫ α).val =
      finiteCyclePushforward
        (closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
          (MorphismProperty.Over.w φ) q a H m)
        (polynomialEndpointMap (m ≫ pullback.fst Y.hom Z.hom ≫ q) a c) := by
  classical
  let f := m ≫ pullback.fst Y.hom Z.hom ≫ q
  let e := closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
    (MorphismProperty.Over.w φ) q a H m
  let s := Function.locallyFinsupp.finite_support c
  let hpt (z : s.toFinset) : IsFiniteCorrespondencePoint Y.hom Z.hom (m z.val) := by
    apply α.property.2
    rw [hα, finiteCyclePushforward_apply_of_isClosedImmersion]
    exact s.mem_toFinset.mp z.property
  let t (z : s.toFinset) := singleFiniteCorrespondence Y.hom Z.hom (m z.val) (hpt z) (c z.val)
  have hsum : (∑ z : s.toFinset, single z.val (c z.val)) = c :=
    (Finset.sum_coe_sort (s := s.toFinset) (f := fun z => single z (c z))).trans
      (sum_apply_smul_single_eq_self_on_univ s)
  have heq : α = ∑ z : s.toFinset, t z := by
    apply Subtype.ext
    calc
      _ = finiteCyclePushforward m c := hα
      _ = finiteCyclePushforward m (∑ z : s.toFinset, single z.val (c z.val)) :=
        congrArg (finiteCyclePushforward m) hsum.symm
      _ = _ := by
        change _ = (finiteCorrespondences Y.hom Z.hom).subtype _
        rw [map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro z _
        exact finiteCyclePushforward_single_of_isClosedImmersion m z.val (c z.val)
  have hc : polynomialEndpointMap f a c =
      ∑ z : s.toFinset, c z.val • polynomialComponentEndpoint f a z.val := by
    calc
      _ = polynomialEndpointMap f a (∑ z : s.toFinset, single z.val (c z.val)) :=
        congrArg (polynomialEndpointMap f a) hsum.symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro z _
        exact polynomialEndpointMap_single f a z.val (c z.val)
  change ((graphFunctor k).map φ ≫ α).val = finiteCyclePushforward e (polynomialEndpointMap f a c)
  rw [heq, Preadditive.comp_sum, hc]
  change (finiteCorrespondences X.hom Z.hom).subtype _ = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [t]
  rw [singleFiniteCorrespondence_eq_zsmul, Preadditive.comp_zsmul]
  change (finiteCorrespondences X.hom Z.hom).subtype (_ • _) = _
  rw [map_zsmul, map_zsmul, polynomialComponentEndpoint, finiteCyclePushforward_comp_apply]
  exact congrArg (fun d : AlgebraicCycle (pullback X.hom Z.hom) ℤ => c z.val • d)
    (graph_comp_closedSupport_single_val_of_admissible φ q a H m z.val (hpt z))

/-- The whole endpoint map when its original parameter is named separately. -/
def closedSupportEndpointMapOfParameterEq (f : D ⟶ Spec (.of (Polynomial k)))
    (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f) :
    fiber f a ⟶ pullback X.hom Z.hom :=
  (pullback.congrHom rfl hf.symm).hom ≫
    closedSupportEndpointMap X.hom Y.hom Z.hom φ.left (MorphismProperty.Over.w φ) q a H m

instance closedSupportEndpointMapOfParameterEq_isClosedImmersion
    (f : D ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f) :
    IsClosedImmersion (closedSupportEndpointMapOfParameterEq φ q a H m f hf) := by
  unfold closedSupportEndpointMapOfParameterEq
  infer_instance

omit [IsNoetherian D] [Flat q] [IsClosedImmersion m] in
@[reassoc]
theorem closedSupportEndpointMapOfParameterEq_ambient
    (f : D ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f) :
    closedSupportEndpointMapOfParameterEq φ q a H m f hf ≫
      correspondenceGraphFiberAmbientMap X.hom Y.hom Z.hom φ.left (MorphismProperty.Over.w φ) =
        inclusion f a ≫ m := by
  rw [closedSupportEndpointMapOfParameterEq, Category.assoc, closedSupportEndpointMap_ambient,
    ← Category.assoc]
  simp only [AffineLineFiber.inclusion, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The whole endpoint formula with the specified original parameter map. -/
theorem graph_comp_closedCycle_endpoint_of_parameter_eq
    (f : D ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f)
    (c : AlgebraicCycle D ℤ) (α : Cor.mk Y ⟶ Cor.mk Z)
    (hα : α.val = finiteCyclePushforward m c) :
    ((graphFunctor k).map φ ≫ α).val =
      finiteCyclePushforward (closedSupportEndpointMapOfParameterEq φ q a H m f hf)
        (polynomialEndpointMap f a c) := by
  subst f
  have he : (pullback.congrHom (rfl : point a = point a) (rfl :
        m ≫ pullback.fst Y.hom Z.hom ≫ q = m ≫ pullback.fst Y.hom Z.hom ≫ q)).hom = 𝟙 _ := by
    simp only [pullback.congrHom_hom, pullback.map_id]
  refine (graph_comp_closedCycle_endpoint φ q a H m c α hα).trans ?_
  apply DFunLike.congr_fun
  apply finiteCyclePushforward_congr
  unfold closedSupportEndpointMapOfParameterEq
  rw [he, Category.id_comp]

end AlgebraicGeometry.Cor
