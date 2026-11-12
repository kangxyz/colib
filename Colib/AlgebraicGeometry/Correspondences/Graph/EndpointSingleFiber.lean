/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiberComponents
public import Colib.AlgebraicGeometry.Correspondences.Graph.AffineLineEndpointCoefficient

/-!
# Actual endpoint graph precomposition of a full integral support fiber

The native graph is expanded over all its source components. Each actual
endpoint incidence has its full fundamental cycle by the constructed Tor
calculation. The disjoint clopen incidence cover then adds back to the entire
scheme-theoretic support fiber. All original generic local lengths and actual
outer maps are retained. No integrality or nonemptiness of the source and no
flatness of the integral support over the cylinder are assumed.

The final theorem uses the existing native additive cylinder and literal
native affine section. It is the prime-support input to whole-family weighted
assembly, not a replacement definition of the span correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

open Stacks.Chow Scheme.PolynomialSectionPencil Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {X Y Z : Scheme.SmoothSite (Spec (.of k))}
  (φ : X ⟶ Y) (q : Y.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
  (hsection : IsPullback φ.left X.hom q (Scheme.AffineLineFiber.point a))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

include hsection in
/-- The actual graph composed with a prime support is the whole endpoint fiber,
for arbitrary smooth sources including disconnected and empty ones. -/
theorem graph_comp_single_val_eq_fiber_of_cartesian_endpoint :
    letI := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left
      (MorphismProperty.Over.w φ) hw
    letI := isNoetherian_correspondenceGraphFiber (X := X.left) Y.hom Z.hom w φ.left hw
    ((graphFunctor k).map φ ≫ singleFiniteCorrespondence Y.hom Z.hom w hw 1).val =
      finiteCyclePushforward
        (correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left (MorphismProperty.Over.w φ))
        (AlgebraicCycle.fundamentalCycle (correspondenceGraphFiber Y.hom Z.hom w φ.left)) := by
  classical
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := Scheme.SmoothSite.isNoetherian_overField k X
  let : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    Scheme.SmoothSite.isLocallyNoetherian_overField k X
  let : IsNormal ((𝟭 Scheme).obj X.left) := Scheme.SmoothSite.isNormal_overField k X
  have := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left
    (MorphismProperty.Over.w φ) hw
  have := isNoetherian_correspondenceGraphFiber (X := X.left) Y.hom Z.hom w φ.left hw
  let F : Fintype (genericPoints X.left) := (finite_genericPoints k (Cor.mk X)).fintype
  let : Fintype (genericPoints ((𝟭 Scheme).obj X.left)) := F
  let z (s : genericPoints X.left) :=
    correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) s.val
  let hz (s : genericPoints X.left) :=
    isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) s
  have : ∀ s : genericPoints X.left,
      IsNoetherian (correspondenceIncidence X.hom Y.hom Z.hom (z s) w) :=
    fun s => isNoetherian_correspondenceIncidence_of_finite_source
      X.hom Y.hom Z.hom (z s) w (hz s) hw
  have : ∀ s : genericPoints X.left,
      IsFinite (correspondenceIncidenceMap X.hom Y.hom Z.hom (z s) w) :=
    fun s => isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom (z s) w (hz s) hw
  rw [graph_comp_single_eq_sum_incidence]
  simp only [one_smul]
  change (finiteCorrespondences X.hom Z.hom).subtype
      (∑ s : genericPoints X.left,
        incidenceTorCorrespondence X.hom Y.hom Z.hom (z s) w (hz s) hw) = _
  rw [map_sum, fundamentalCycle_graphFiber_eq_sum_incidence
    X.hom Y.hom Z.hom φ.left (MorphismProperty.Over.w φ) w, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  let m := correspondenceIncidenceMap X.hom Y.hom Z.hom (z s) w
  let l := correspondenceLeftGraphFiberMap X.hom Y.hom Z.hom φ.left
    (MorphismProperty.Over.w φ) w s.val
  let r := correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left (MorphismProperty.Over.w φ)
  let c := AlgebraicCycle.fundamentalCycle (correspondenceIncidence X.hom Y.hom Z.hom (z s) w)
  have : IsFinite m := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom (z s) w (hz s) hw
  have h₁ := incidenceTorCorrespondence_val X.hom Y.hom Z.hom (z s) w (hz s) hw
  have h₂ := congrArg (finiteCyclePushforward m)
    (incidenceTorCycle_eq_fundamentalCycle_of_cartesian_endpoint
      X.hom Y.hom Z.hom φ.left (MorphismProperty.Over.w φ) q a hsection s w hw)
  have hp {D E : Scheme.{u}} (f g : D ⟶ E) [IsFinite f] [IsFinite g] (h : f = g)
      (c : AlgebraicCycle D ℤ) : finiteCyclePushforward f c = finiteCyclePushforward g c := by
    cases h
    rfl
  have h₃ := hp (l ≫ r) m
    (correspondenceLeftGraphFiberMap_outer X.hom Y.hom Z.hom φ.left
      (MorphismProperty.Over.w φ) w s.val) c
  exact h₁.trans (h₂.trans (h₃.symm.trans (finiteCyclePushforward_comp_apply l r c).symm))

variable (U V : Scheme.SmoothSite (Spec (.of k))) (r : k)

/-- Literal native 0/1 graph precomposition preserves the full support fiber
and its nilpotent multiplicities. The scalar is arbitrary, so zero and one
require no separate extra hypotheses. -/
theorem nativeSection_comp_single_val_eq_fiber
    (w : pullback (C := Scheme) (affineLineCylinder.obj U).hom V.hom)
    (hw : IsFiniteCorrespondencePoint (affineLineCylinder.obj U).hom V.hom w) :
    let σ := nativeAffineSection (.of k) U r
    letI := isFinite_correspondenceGraphFiberMap U.hom (affineLineCylinder.obj U).hom
      V.hom w σ.left (MorphismProperty.Over.w σ) hw
    letI := isNoetherian_correspondenceGraphFiber (X := U.left)
      (affineLineCylinder.obj U).hom V.hom w σ.left hw
    ((graphFunctor k).map σ ≫
      singleFiniteCorrespondence (affineLineCylinder.obj U).hom V.hom w hw 1).val =
      finiteCyclePushforward
        (correspondenceGraphFiberMap U.hom (affineLineCylinder.obj U).hom V.hom w σ.left
          (MorphismProperty.Over.w σ))
        (AlgebraicCycle.fundamentalCycle
          (correspondenceGraphFiber (affineLineCylinder.obj U).hom V.hom w σ.left)) := by
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let q := (nativeParameterIso (.of k) U).hom ≫ pullback.snd U.hom p
  have : Flat (pullback.snd U.hom p) := Flat.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback U.hom p) (inferInstance : Flat U.hom)
  have : Flat q := by
    change Flat ((nativeParameterIso (.of k) U).hom ≫ pullback.snd U.hom p)
    infer_instance
  exact graph_comp_single_val_eq_fiber_of_cartesian_endpoint
    (nativeAffineSection (.of k) U r) q r (nativeSection_affineLine_isPullback r U) w hw

end AlgebraicGeometry.Cor
