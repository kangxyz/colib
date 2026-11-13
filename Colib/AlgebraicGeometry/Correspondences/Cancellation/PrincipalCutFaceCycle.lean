/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PrincipalCutFace

/-!
# Graph-face compatibility of an admissible principal cut

When the cut and the component cut on the face both define finite
correspondences, local proper intersection at their common points over
generic source points suffices for equality of the two correspondences.
All other coefficients vanish by the actual closed support and the
generic-source condition for finite correspondences.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber AlgebraicCycle Stacks.Chow

private theorem finiteCyclePushforward_apply_eq_zero_off_range {D E : Scheme.{u}}
    (j : D ⟶ E) [IsFinite j] (c : AlgebraicCycle D ℤ) (x : E) (hx : x ∉ Set.range j) :
    finiteCyclePushforward j c x = 0 := by
  by_contra hn
  obtain ⟨y, _, hy⟩ := finiteCyclePushforward_support_subset j c hn
  exact hx ⟨y, hy⟩

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsNoetherian P]

private theorem polynomialEndpointMap_fundamentalFiber_apply_eq_cut_off_range
    (f g : P ⟶ Spec (.of (Polynomial k))) (a b : k) (x : fiber f a)
    (hx : inclusion f a x ∉ Set.range (inclusion g b)) :
    polynomialEndpointMap f a (finiteCyclePushforward (inclusion g b)
        (fundamentalCycle (fiber g b))) x =
      finiteCyclePushforward (inclusion (inclusion f a ≫ g) b)
        (polynomialEndpointMap (inclusion f a ≫ g) b (fundamentalCycle (fiber f a))) x := by
  let i := inclusion f a
  let j := inclusion g b
  let d := AffineLineFiber.fiberMap f a j
  let e := inclusion (i ≫ g) b
  have hd : x ∉ Set.range d := by
    rintro ⟨y, hy⟩
    apply hx
    refine ⟨inclusion (j ≫ f) a y, ?_⟩
    exact (congrArg (fun m : fiber (j ≫ f) a ⟶ P => m y) (fiberMap_inclusion f a j)).symm.trans
      (congrArg i hy)
  have he : x ∉ Set.range e := by
    rintro ⟨y, hy⟩
    apply hx
    refine ⟨AffineLineFiber.fiberMap g b i y, ?_⟩
    exact (congrArg (fun m : fiber (i ≫ g) b ⟶ P => m y) (fiberMap_inclusion g b i)).trans
      (congrArg i hy)
  rw [polynomialEndpointMap_pushforward_closed f a j (fundamentalCycle (fiber g b))]
  exact (finiteCyclePushforward_apply_eq_zero_off_range d _ x hd).trans
    (finiteCyclePushforward_apply_eq_zero_off_range e _ x he).symm

variable {X Y Z : SmoothSite (Spec (.of k))}
  (φ : X ⟶ Y) (q : Y.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
  (H : IsPullback φ.left X.hom q (point a))
  (m : P ⟶ pullback Y.hom Z.hom) [IsClosedImmersion m]

/-- Graph precomposition commutes with the actual component cut after the
face fibre, given admissibility and the local proper-intersection hypotheses
at the common cut points over the generic source. -/
theorem graph_comp_closedFiberCycle_endpoint_eq
    (f : P ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f)
    (g : P ⟶ Spec (.of (Polynomial k))) (b : k)
    (α : Cor.mk Y ⟶ Cor.mk Z)
    (hα : α.val = finiteCyclePushforward m
      (finiteCyclePushforward (inclusion g b) (fundamentalCycle (fiber g b))))
    (β : Cor.mk X ⟶ Cor.mk Z)
    (hβ : β.val = finiteCyclePushforward (closedSupportEndpointMapOfParameterEq φ q a H m f hf)
      (finiteCyclePushforward (inclusion (inclusion f a ≫ g) b)
        (polynomialEndpointMap (inclusion f a ≫ g) b (fundamentalCycle (fiber f a)))))
    (hcut : ∀ x : fiber f a,
      pullback.fst X.hom Z.hom (closedSupportEndpointMapOfParameterEq φ q a H m f hf x)
        ∈ genericPoints X.left →
      inclusion f a x ∈ Set.range (inclusion g b) →
      let R := P.presheaf.stalk (inclusion f a x)
      let t := scalar f a (inclusion f a x)
      let s := scalar g b (inclusion f a x)
      IsSMulRegular R t ∧ IsSMulRegular R s ∧
        Module.length R (R ⧸ (Ideal.span {t} ⊔ Ideal.span {s})) ≠ ⊤ ∧
        (∀ r : PrimeSpectrum R, r.asIdeal ∈ (Ideal.span {s}).minimalPrimes → t ∉ r.asIdeal) ∧
        (∀ r : PrimeSpectrum R, r.asIdeal ∈ (Ideal.span {t}).minimalPrimes → s ∉ r.asIdeal)) :
    (graphFunctor k).map φ ≫ α = β := by
  let e : fiber f a ⟶ pullback X.hom Z.hom :=
    closedSupportEndpointMapOfParameterEq φ q a H m f hf
  let γ : finiteCorrespondences X.hom Z.hom := (graphFunctor k).map φ ≫ α
  let δ : finiteCorrespondences X.hom Z.hom := β
  let c := polynomialEndpointMap f a
    (finiteCyclePushforward (inclusion g b) (fundamentalCycle (fiber g b)))
  let d := finiteCyclePushforward (inclusion (inclusion f a ≫ g) b)
    (polynomialEndpointMap (inclusion f a ≫ g) b (fundamentalCycle (fiber f a)))
  have hγ : γ.val = finiteCyclePushforward e c :=
    graph_comp_closedCycle_endpoint_of_parameter_eq φ q a H m f hf _ α hα
  have hδ : δ.val = finiteCyclePushforward e d := hβ
  change γ = δ
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro w
  change γ.val w = δ.val w
  by_cases hw : w ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hw
    have heγ := (DFunLike.congr_fun hγ (e x)).trans
      (finiteCyclePushforward_apply_of_isClosedImmersion e c x)
    have heδ := (DFunLike.congr_fun hδ (e x)).trans
      (finiteCyclePushforward_apply_of_isClosedImmersion e d x)
    by_cases hg : pullback.fst X.hom Z.hom (e x) ∈ genericPoints X.left
    · by_cases hx : inclusion f a x ∈ Set.range (inclusion g b)
      · obtain ⟨hrf, hrg, hfin, hproperf, hproperg⟩ := hcut x hg hx
        exact (graph_comp_closedFiberCycle_endpoint_apply_eq_cut φ q a H m f hf g b α hα
          x hx hrf hrg hfin hproperf hproperg).trans heδ.symm
      · exact heγ.trans
          ((polynomialEndpointMap_fundamentalFiber_apply_eq_cut_off_range f g a b x hx).trans
            heδ.symm)
    · exact (finiteCorrespondence_apply_eq_zero_of_notMem_genericSource
        X.hom Z.hom γ (e x) hg).trans
        (finiteCorrespondence_apply_eq_zero_of_notMem_genericSource X.hom Z.hom δ (e x) hg).symm
  · have hzγ := (DFunLike.congr_fun hγ w).trans
      (finiteCyclePushforward_apply_eq_zero_off_range e c w hw)
    have hzδ := (DFunLike.congr_fun hδ w).trans
      (finiteCyclePushforward_apply_eq_zero_off_range e d w hw)
    exact hzγ.trans hzδ.symm

end AlgebraicGeometry.Cor
