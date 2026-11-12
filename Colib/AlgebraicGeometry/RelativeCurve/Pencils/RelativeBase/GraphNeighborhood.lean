/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeGraphDivisor

/-!
# Simultaneous genuine graph and coefficient frames over a relative base

The parameter neighborhood contains the specified point and the images of the
entire finite marked fibre. Finite closed-image avoidance then retains the full
marked scheme over a common principal base neighborhood. Both boundary
coefficient frames are constructed there and all their powers use this same
neighborhood. No fibrewise frame is substituted for a frame on the open scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Z : Scheme.{u}} (q : X ⟶ S) (z : Z ⟶ X)

/-- The actual marked graph, in parameter-first order. -/
def relativeBoundaryGraph : Z ⟶ pullback q (z ≫ q) :=
  pullback.lift z (𝟙 Z) (by simp)

@[reassoc (attr := simp)]
theorem relativeBoundaryGraph_fst :
    relativeBoundaryGraph q z ≫ pullback.fst q (z ≫ q) = z := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relativeBoundaryGraph_snd :
    relativeBoundaryGraph q z ≫ pullback.snd q (z ≫ q) = 𝟙 Z := pullback.lift_snd _ _ _

instance [IsSeparated q] : IsClosedImmersion (relativeBoundaryGraph q z) := by
  have : IsClosedImmersion (relativeBoundaryGraph q z ≫ pullback.snd q (z ≫ q)) := by
    rw [relativeBoundaryGraph_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd q (z ≫ q))

instance [IsSeparated q] [SmoothOfRelativeDimension 1 q] :
    IsEffectiveCartierDivisor (relativeBoundaryGraph q z).ker := by
  have : SmoothOfRelativeDimension 1 (pullback.snd q (z ≫ q)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback q (z ≫ q)) inferInstance
  exact Stacks.Hilbert.isEffectiveCartierDivisor_ker_section
    (f := pullback.snd q (z ≫ q)) (relativeBoundaryGraph q z)
    (relativeBoundaryGraph_snd q z)

variable [IsAffine X] [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  [IsFinite (z ≫ q)]

/-- A principal parameter neighborhood carries a genuine graph-line frame above
all points of any prescribed finite parameter set. -/
theorem exists_principalRelativeBoundaryFrame (E : Set X) (hE : E.Finite) :
    ∃ u : Γ(X, ⊤), E ⊆ X.basicOpen u ∧
      Nonempty ((divisorSheaf (relativeBoundaryGraph q z).ker).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).ι ≅
          SheafOfModules.unit
            ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).toScheme.ringCatSheaf) :=
  exists_principalFiniteTargetFrame (pullback.fst q (z ≫ q))
    (divisorSheaf (relativeBoundaryGraph q z).ker) E hE

/-- The parameter neighborhood contains the point and every marked point over
its base value. The subsequent base neighborhood retains the whole marked
scheme, not just these points or their reductions. -/
theorem exists_relativeBoundaryFrame_with_whole_mark (x : X) :
    ∃ u : Γ(X, ⊤), x ∈ X.basicOpen u ∧
      ∃ V : S.Opens, q x ∈ V ∧
        (∀ b : Z, (z ≫ q) b ∈ V → z b ∈ X.basicOpen u) ∧
        Nonempty ((divisorSheaf (relativeBoundaryGraph q z).ker).restrict
          ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).ι ≅
            SheafOfModules.unit
              ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).toScheme.ringCatSheaf) := by
  let E : Set X := insert x (z '' ((z ≫ q) ⁻¹' {q x}))
  have hE : E.Finite := (((z ≫ q).finite_preimage_singleton (q x)).image z).insert x
  obtain ⟨u, hEu, e⟩ := exists_principalRelativeBoundaryFrame q z E hE
  have hfibre : (z ≫ q) ⁻¹' {q x} ⊆ (z ⁻¹ᵁ X.basicOpen u : Set Z) := by
    intro b hb
    exact hEu (Set.mem_insert_of_mem _ ⟨b, hb, rfl⟩)
  obtain ⟨V, hV, hxV, hVU⟩ := Stacks.SheafOfModules.exists_isOpen_mem_preimage_subset
    (z ≫ q).isClosedMap (z ⁻¹ᵁ X.basicOpen u).isOpen hfibre
  exact ⟨u, hEu (Set.mem_insert x _), ⟨V, hV⟩, hxV, fun b hb => hVU hb, e⟩

variable [IsAffine S] {C D : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C)
  [IsFinite (d ≫ π)] (s : Z ⟶ C)
  (L : C.Modules) [IsInvertibleModule C L]

/-- One principal base neighborhood simultaneously supplies the genuine graph
frame and both full finite-boundary coefficient frames. The source parameter
open is explicit and may restrict the entire diagram; it is not a hidden
restriction of only the correction source. -/
theorem exists_simultaneousPrincipalBoundaryFrames (x : X) :
    ∃ u : Γ(X, ⊤), x ∈ X.basicOpen u ∧
      ∃ v : Γ(S, ⊤), q x ∈ S.basicOpen v ∧
        (∀ b : Z, (z ≫ q) b ∈ S.basicOpen v → z b ∈ X.basicOpen u) ∧
        Nonempty ((divisorSheaf (relativeBoundaryGraph q z).ker).restrict
          ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).ι ≅
            SheafOfModules.unit
              ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).toScheme.ringCatSheaf) ∧
        Nonempty (((Modules.pullback d).obj L).restrict ((d ≫ π) ⁻¹ᵁ S.basicOpen v).ι ≅
          SheafOfModules.unit ((d ≫ π) ⁻¹ᵁ S.basicOpen v).toScheme.ringCatSheaf) ∧
        Nonempty (((Modules.pullback s).obj L).restrict ((z ≫ q) ⁻¹ᵁ S.basicOpen v).ι ≅
          SheafOfModules.unit ((z ≫ q) ⁻¹ᵁ S.basicOpen v).toScheme.ringCatSheaf) := by
  obtain ⟨u, hxu, W, hxW, hmark, eG⟩ := exists_relativeBoundaryFrame_with_whole_mark q z x
  obtain ⟨v, hxv, hvW, eD, eZ⟩ := exists_commonPrincipalBoundaryFrames
    (d ≫ π) (z ≫ q) ((Modules.pullback d).obj L) ((Modules.pullback s).obj L) (q x) W hxW
  exact ⟨u, hxu, v, hxv, fun b hb => hmark b (hvW hb), eG, eD, eZ⟩

/-- All coefficient powers are produced after the same neighborhoods have been
chosen. No degree-dependent shrinking or prescribed power-frame input occurs. -/
theorem exists_simultaneousPrincipalBoundaryPowerFrames (x : X) :
    ∃ u : Γ(X, ⊤), x ∈ X.basicOpen u ∧
      ∃ v : Γ(S, ⊤), q x ∈ S.basicOpen v ∧
        (∀ b : Z, (z ≫ q) b ∈ S.basicOpen v → z b ∈ X.basicOpen u) ∧
        Nonempty ((divisorSheaf (relativeBoundaryGraph q z).ker).restrict
          ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).ι ≅
            SheafOfModules.unit
              ((pullback.fst q (z ≫ q)) ⁻¹ᵁ X.basicOpen u).toScheme.ringCatSheaf) ∧
        ∀ n : ℤ,
          Nonempty ((Modules.pullback (((d ≫ π) ⁻¹ᵁ S.basicOpen v).ι ≫ d)).obj
            (tensorPowModule C L n) ≅
              SheafOfModules.unit ((d ≫ π) ⁻¹ᵁ S.basicOpen v).toScheme.ringCatSheaf) ∧
          Nonempty ((Modules.pullback (((z ≫ q) ⁻¹ᵁ S.basicOpen v).ι ≫ s)).obj
            (tensorPowModule C L n) ≅
              SheafOfModules.unit ((z ≫ q) ⁻¹ᵁ S.basicOpen v).toScheme.ringCatSheaf) := by
  obtain ⟨u, hxu, v, hxv, hmark, eG, ⟨eD⟩, ⟨eZ⟩⟩ :=
    exists_simultaneousPrincipalBoundaryFrames q z π d s L x
  let ED := wholeBoundaryPullbackFrame (d ≫ π) d L (S.basicOpen v) eD
  let EZ := wholeBoundaryPullbackFrame (z ≫ q) s L (S.basicOpen v) eZ
  exact ⟨u, hxu, v, hxv, hmark, eG, fun n =>
    ⟨exists_tensorPowModule_boundaryFrame _ L ED n,
      exists_tensorPowModule_boundaryFrame _ L EZ n⟩⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
