/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GeneratedDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RetainedIdeals
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionCorrespondences
public import Colib.AlgebraicGeometry.Correspondences.Graph.IdealProductPencilEndpoints
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
/-! # The genuine relative two-source signed pencil -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor
open PolynomialSectionPencil SmoothSite.Contraction
set_option backward.isDefEq.respectTransparency false

local instance (A : Scheme.{u}) (M : A.Modules) [hM : IsInvertibleModule A M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property M := hM

variable {S X C Y A B Z D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range z))

variable {k : Type u} [Field k] (t : S ⟶ Spec (.of k)) [Smooth t]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "σ" => divisorSheafGlobalSection (Scheme.Hom.ker (compactificationGraph π j))
local notation "gA" => commonToLambda π j α
local notation "gN" => commonToPsi (q) π j p hq a α β h
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (q) π j p hq a
  (z) s hs d
local notation "i" => commonBoundaryInclusion π j α s d
local notation "qB" => commonProjection π j α

variable [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsOpenImmersion a]
  {V : Scheme.{u}} [IsAffine V] (v : V ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
  (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)

local instance : Smooth (j ≫ π) := SmoothOfRelativeDimension.smooth 1 (j ≫ π)
local instance : Smooth (v ≫ π) := SmoothOfRelativeDimension.smooth 1 (v ≫ π)
local instance : Smooth q := SmoothOfRelativeDimension.smooth 1 q

local notation "qA" => j ≫ π
local notation "qN" => a ≫ q
local notation "rV" => v ≫ π
local notation "rB" => retainedProductInclusion qB π v
local notation "rA" => retainedProductInclusion qA π v
local notation "rN" => retainedProductInclusion qN π v
local notation "hβ" => Eq.symm (commonProjection_fixed q π j p hq a α β h)
local notation "hφb" => retainedTarget_base π v j α φ hφ
local notation "jA" => retainedSourceChange qA qB rV α rfl
local notation "jN" => retainedSourceChange qN qB rV β hβ
local notation "U" => SmoothSite.mk (qB ≫ t)
local notation "UA" => SmoothSite.mk (qA ≫ t)
local notation "UN" => SmoothSite.mk (qN ≫ t)
local notation "W" => SmoothSite.mk (rV ≫ t)
local notation "αs" => SmoothSite.homMk (X := U) (Y := UA) α
  (Eq.symm (Category.assoc α qA t))
local notation "βs" => SmoothSite.homMk (X := U) (Y := UN) β
  (Eq.trans (Eq.symm (Category.assoc β qN t)) (congrArg (fun f => f ≫ t) hβ))
local notation "φs" => SmoothSite.homMk (X := U) (Y := W) φ
  (Eq.trans (Eq.symm (Category.assoc φ rV t)) (congrArg (fun f => f ≫ t) hφb))

section SectionMethods

variable {q π j p hq a z s hs H e d hd ha}

set_option maxHeartbeats 500000 in
-- Elaborate both chosen relative lines and the actual signed endpoints together.
/-- The actual signed endpoint laws for the two named correspondences of this section data. -/
theorem SectionData.exists_signedEndpoints_for_lambda_psi
    (c : SectionData q π j p hq a z s hs H e d hd ha) :
    ∃ δ : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W,
      (Cor.graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ δ =
          (Cor.graphFunctor k).map φs ∧
        (Cor.graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
          (Cor.graphFunctor k).map αs ≫ c.lambda t v hc -
            (Cor.graphFunctor k).map βs ≫ c.psi t v hc := by
  let := c.T_invertible
  let := c.N_invertible
  let : IsInvertibleModule (pullback qA π) (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf (pullback qA π) F c.T
      (inferInstanceAs (IsInvertibleModule (pullback qA π) F)) c.T_invertible
  let IA := (zeroScheme _ (tensorModules F c.T) c.aS).comap rA
  let IB := (zeroScheme _ c.T c.bS).comap rA
  let IN := (zeroScheme _ c.N c.nS).comap rN
  let ID := (zeroScheme _ c.N c.dS).comap rN
  let LL : (pullback qB rV).Modules := (Modules.pullback rB).obj (c.commonLine α β h)
  let PP : (pullback qB rV).Modules := (Modules.pullback rB).obj (c.commonPoleLine α β h)
  let hLine : IsInvertibleModule (pullback qB rV) LL :=
    c.commonLine_pullback_invertible α β h rB
  let hPole : IsInvertibleModule (pullback qB rV) PP :=
    c.commonPoleLine_pullback_invertible α β h rB
  let : AlgebraicGeometry.SheafOfModules.IsInvertible (pullback qB rV).sheaf.obj
      (pullback qB rV).ringCatSheaf.property LL := hLine
  let : AlgebraicGeometry.SheafOfModules.IsInvertible (pullback qB rV).sheaf.obj
      (pullback qB rV).ringCatSheaf.property PP := hPole
  let s₀ : Γ(LL, ⊤) := pullbackGlobalSections rB _ (c.commonStart α β h)
  let s₁ : Γ(LL, ⊤) := pullbackGlobalSections rB _ (c.commonEnd α β h)
  let u : Γ(PP, ⊤) := pullbackGlobalSections rB _ (c.commonPole α β h)
  have hAB :
      (IsFinite (IA.subschemeι ≫ pullback.fst qA rV) ∧
        IsRelativeEffectiveCartierDivisor (pullback.fst qA rV) IA) ∧
      (IsFinite (IB.subschemeι ≫ pullback.fst qA rV) ∧
        IsRelativeEffectiveCartierDivisor (pullback.fst qA rV) IB) := by
    exact c.retainedFirstFactors_comap_finite_relativeCartier v hc
  have hND :
      (IsFinite (IN.subschemeι ≫ pullback.fst qN rV) ∧
        IsRelativeEffectiveCartierDivisor (pullback.fst qN rV) IN) ∧
      (IsFinite (ID.subschemeι ≫ pullback.fst qN rV) ∧
        IsRelativeEffectiveCartierDivisor (pullback.fst qN rV) ID) := by
    exact c.retainedCorrectionFactors_comap_finite_relativeCartier v hc
  let := hAB.1.1
  let := hAB.1.2.2
  let := hAB.2.1
  let := hAB.2.2.2
  let := hND.1.1
  let := hND.1.2.2
  let := hND.2.1
  let := hND.2.2.2
  have hf := c.retainedFamily_finite_flat α β h t v hc
  let := hf.1
  let := hf.2
  have hp : IsFinite ((zeroScheme _ PP u).subschemeι ≫ pullback.fst qB rV) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst qB rV) (zeroScheme _ PP u) :=
    c.retainedPole_finite_relativeCartier α β h v hc
  have hFamilyFin : IsFinite (Cor.nativeRetainedFamilySource (k := k) t qB rV LL s₀ s₁) := by
    unfold Cor.nativeRetainedFamilySource
    infer_instance
  have hFamilyFlat : Flat (Cor.nativeRetainedFamilySource (k := k) t qB rV LL s₀ s₁) := by
    unfold Cor.nativeRetainedFamilySource
    infer_instance
  have : Flat jA := MorphismProperty.of_isPullback
    (retainedSourceChange_isPullback qA qB rV α rfl).flip inferInstance
  have : Flat jN := MorphismProperty.of_isPullback
    (retainedSourceChange_isPullback qN qB rV β hβ).flip inferInstance
  let pencilWitnesses : Cor.RetainedPencilWitnesses (k := k) t qB rV LL PP s₀ s₁ u :=
    ⟨hFamilyFin, hFamilyFlat, hp.1, hp.2.2⟩
  let δ := Cor.retainedPencilDifferenceFromWitnesses (k := k) t qB rV LL PP s₀ s₁ u pencilWitnesses
  refine ⟨δ, ?_⟩
  exact Cor.retainedIdealDifference_source_endpoints (k := k) t qB rV qA qN
    α rfl β hβ φ hφb LL PP s₀ s₁ u IA IB IN ID pencilWitnesses
    (isPullbackDefined_of_flat jA IA hAB.1.2.1)
    (isPullbackDefined_of_flat jA IB hAB.2.2.1)
    (isPullbackDefined_of_flat jN IN hND.1.2.1)
    (isPullbackDefined_of_flat jN ID hND.2.2.1) hp.2.1
    (c.retainedStart_zeroScheme α β h v φ hφ)
    (c.retainedEnd_zeroScheme α β h v)
    (c.retainedPole_zeroScheme α β h v)

include hc in
/-- The generated pencil uses the correspondences defined by the same section data. -/
theorem SectionData.exists_signedEndpoints
    (c : SectionData q π j p hq a z s hs H e d hd ha) :
    ∃ lam : Cor.mk UA ⟶ Cor.mk W,
      ∃ psi : Cor.mk UN ⟶ Cor.mk W,
        ∃ δ : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W,
          (Cor.graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ δ =
              (Cor.graphFunctor k).map φs ∧
            (Cor.graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
              (Cor.graphFunctor k).map αs ≫ lam - (Cor.graphFunctor k).map βs ≫ psi := by
  obtain ⟨δ, h₀, h₁⟩ := c.exists_signedEndpoints_for_lambda_psi t α β h v hc φ hφ
  exact ⟨c.lambda t v hc, c.psi t v hc, δ, h₀, h₁⟩

end SectionMethods

variable [IsLocallyNoetherian S] [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]

include z s hs H e d hd ha hc in
/-- The actual two relative Serre constructions produce the signed pencil.
The three frames here are intermediate outputs of the common-neighborhood
construction, eliminated by the final simultaneous-refinement theorem. -/
theorem exists_signedPencil_of_constructedFrames
    (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)
    (eD : (Modules.pullback d).obj L ≅ SheafOfModules.unit D.ringCatSheaf)
    (eZ : (Modules.pullback (s ≫ j)).obj L ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ lam : Cor.mk UA ⟶ Cor.mk W,
      ∃ psi : Cor.mk UN ⟶ Cor.mk W,
        ∃ δ : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W,
          (Cor.graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ δ =
              (Cor.graphFunctor k).map φs ∧
            (Cor.graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
              (Cor.graphFunctor k).map αs ≫ lam - (Cor.graphFunctor k).map βs ≫ psi := by
  obtain ⟨c⟩ := nonempty_sectionData q π j p hq a z s hs H e d hd ha L hL eD eZ
  exact c.exists_signedEndpoints t α β h v hc φ hφ

include z s hs H e d hd ha hc in
/-- Coefficient homotopy invariance consumes the genuinely generated relative
pencil; no endpoint or zero-open provider occurs in the input. -/
theorem hasRestrictionDifferenceLifting_of_constructedFrames
    (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)
    (eD : (Modules.pullback d).obj L ≅ SheafOfModules.unit D.ringCatSheaf)
    (eZ : (Modules.pullback (s ≫ j)).obj L ≅ SheafOfModules.unit Z.ringCatSheaf)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    PresheafWithTransfers.HasRestrictionDifferenceLifting P φs βs αs := by
  obtain ⟨lam, psi, δ, h₀, h₁⟩ := exists_signedPencil_of_constructedFrames
    q π j p hq a z s hs H e d hd ha t α β h v hc φ hφ L hL eD eZ
  exact PresheafWithTransfers.hasRestrictionDifferenceLifting_of_homotopy
    P hP φs βs αs lam psi δ h₀ h₁

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
