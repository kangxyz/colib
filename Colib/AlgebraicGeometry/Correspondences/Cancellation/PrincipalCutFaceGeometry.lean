/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PrincipalCutFaceCycle
import Colib.AlgebraicGeometry.Chow.FiniteDoubleCut
import Colib.AlgebraicGeometry.Chow.ProperDoubleCut

/-!
# Face compatibility from a finite principal cut

The actual source projection of the face support is Cartesian. A finite
original cut and its generic image condition then supply the finite stalk
colength and both proper-intersection conditions at the face.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber AlgebraicCycle Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (φ : X ⟶ Y) (q : Y.left ⟶ Spec (.of (Polynomial k))) (a : k)
  (H : IsPullback φ.left X.hom q (point a))
  (m : P ⟶ pullback Y.hom Z.hom)

/-- The actual closed-support endpoint is Cartesian on its source coordinate. -/
theorem closedSupportEndpointMapOfParameterEq_isPullback_fst
    (f : P ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f) :
    IsPullback
      (closedSupportEndpointMapOfParameterEq φ q a H m f hf ≫ pullback.fst X.hom Z.hom)
      (inclusion f a) φ.left (m ≫ pullback.fst Y.hom Z.hom) := by
  subst f
  let p := m ≫ pullback.fst Y.hom Z.hom
  let e := closedSupportEndpointIso X.hom Y.hom Z.hom φ.left q a H m
  refine (IsPullback.of_hasPullback φ.left p).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp [p])
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [closedSupportEndpointMapOfParameterEq]
    have he : (pullback.congrHom (rfl : point a = point a)
        (rfl : m ≫ pullback.fst Y.hom Z.hom ≫ q = m ≫ pullback.fst Y.hom Z.hom ≫ q)).hom =
        𝟙 _ := by
      simp only [pullback.congrHom_hom, pullback.map_id]
    rw [he, Category.id_comp, closedSupportEndpointMap_fst]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      closedSupportEndpointIso_total X.hom Y.hom Z.hom φ.left q a H m

variable [IsNoetherian P] [IsClosedImmersion m] [Flat q]

/-- The two actual finite correspondences agree after a Cartesian graph
face, using finiteness and generic dominance of the original cut and
regularity of both equations in the original support stalks. -/
@[colib_tag "COL-1041", colib_ref "Voevodsky2010Cancellation"
  "Section 3, Proposition 3.1, pp. 676–677" "adaptation"
  "Cycle coefficients for a Cartesian closed polynomial face of a principal cut"]
theorem graph_comp_closedFiberCycle_endpoint_eq_of_finite
    (f : P ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f)
    (g : P ⟶ Spec (.of (Polynomial k))) (b : k)
    [IsFinite (inclusion g b ≫ (m ≫ pullback.fst Y.hom Z.hom))]
    (hgen : ∀ y : genericPoints (fiber g b),
      (m ≫ pullback.fst Y.hom Z.hom) (inclusion g b y.val) ∈ genericPoints Y.left)
    (hrf : ∀ x : P, IsSMulRegular (P.presheaf.stalk x) (scalar f a x))
    (hrg : ∀ x : P, IsSMulRegular (P.presheaf.stalk x) (scalar g b x))
    (α : Cor.mk Y ⟶ Cor.mk Z)
    (hα : α.val = finiteCyclePushforward m
      (finiteCyclePushforward (inclusion g b) (fundamentalCycle (fiber g b))))
    (β : Cor.mk X ⟶ Cor.mk Z)
    (hβ : β.val = finiteCyclePushforward (closedSupportEndpointMapOfParameterEq φ q a H m f hf)
      (finiteCyclePushforward (inclusion (inclusion f a ≫ g) b)
        (polynomialEndpointMap (inclusion f a ≫ g) b (fundamentalCycle (fiber f a))))) :
    (graphFunctor k).map φ ≫ α = β := by
  let p := m ≫ pullback.fst Y.hom Z.hom
  let v := closedSupportEndpointMapOfParameterEq φ q a H m f hf ≫ pullback.fst X.hom Z.hom
  have hv := closedSupportEndpointMapOfParameterEq_isPullback_fst φ q a H m f hf
  refine graph_comp_closedFiberCycle_endpoint_eq φ q a H m f hf g b α hα β hβ ?_
  intro x hx _
  let y := inclusion f a x
  let R := P.presheaf.stalk y
  let t := scalar f a y
  let s := scalar g b y
  have hfin := doubleCut_length_ne_top_of_finite f a (inclusion g b) p φ.left v hv x hx
  rw [inclusion_stalk] at hfin
  have hscalar : scalar (p ≫ q) a y = t :=
    congrArg (fun l : P ⟶ Spec (.of (Polynomial k)) => scalar l a y)
      ((Category.assoc m (pullback.fst Y.hom Z.hom) q).trans hf)
  have hproper (r : PrimeSpectrum R) (hr : r.asIdeal ∈ (Ideal.span {s}).minimalPrimes) :
      t ∉ r.asIdeal := by
    rw [← hscalar]
    exact scalar_notMem_minimalPrimes_of_cut_genericImage p q a g b hgen y r hr
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_left.mpr
    (fun w hw => hrg y (hw.trans (mul_zero s).symm))
  exact ⟨hrf y, hrg y, hfin, hproper, Ideal.notMem_minimalPrimes_span_singleton_symm hs hproper⟩

end AlgebraicGeometry.Cor
