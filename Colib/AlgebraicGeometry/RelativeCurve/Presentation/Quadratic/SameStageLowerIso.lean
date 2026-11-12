/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialTailInduction
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageOriginalMark
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLowerTail
/-! # Apply the real polynomial-tail induction hypothesis to the selected lower tail

The named conclusion is exactly the lower isomorphism used by the localized
restriction consumer. The actual rational marking supplies its coefficient
residue separability, and the induction hypothesis supplies the structural
isomorphism. Only the proved equality of base markings is transported.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart
attribute [local instance] SameStageLocalizedInputs.ring
  SameStageLocalizedInputs.tailSmooth SameStageLocalizedInputs.tailSeparated
  SameStageLocalizedInputs.tailQuasiCompact
local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))
variable {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω]

/-- The consumer's lower isomorphism, keeping its actual original-base marking. -/
def SameStageLocalizedInputs.LowerIsomorphism (G : SameStageLocalizedInputs K Ω)
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Prop :=
  let : IsAffine (SmoothSite.mk G.tail).left := inferInstanceAs (IsAffine (Spec (.of G.R)))
  IsIso (etaleNeighborhoodValuePullback G.tailToBase (ξ := G.η) G.originalMark_base.symm Q)

/-- Only the target marking equality is transported; the underlying structural map is unchanged. -/
theorem SameStageLocalizedInputs.lowerIsomorphism_of_structural_iso
    (G : SameStageLocalizedInputs K Ω)
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : let : IsAffine (SmoothSite.mk G.tail).left :=
        inferInstanceAs (IsAffine (Spec (.of G.R)))
      IsIso (etaleNeighborhoodValuePullback G.tailToBase (ξ := G.η) rfl Q)) :
    G.LowerIsomorphism Q := by
  let : IsAffine (SmoothSite.mk G.tail).left := inferInstanceAs (IsAffine (Spec (.of G.R)))
  have htransport (ζ : Spec (.of Ω) ⟶ (base (Spec (.of K))).left)
      (hζ : G.η ≫ G.tail = ζ) :
      IsIso (etaleNeighborhoodValuePullback G.tailToBase (ξ := G.η) hζ Q) := by
    subst ζ
    exact h
  exact htransport _ G.originalMark_base.symm

/-- Instantiate lower-dimensional polynomial-tail induction on the actual selected tail. -/
theorem sameStageLocalizedInputs_lower_iso
    (K F E B : Type u) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [CommRing B] [Algebra F B] [Algebra K B] [IsScalarTower K F B]
    [Algebra.Smooth F B]
    (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E)
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P0 : Spec (.of (E ⊗[F] B))) (re r : E ⊗[F] B)
    (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[F] B))) (hxE : xE default = P0)
    (hre : re ∉ (xE default).asIdeal)
    (he : ((algebraMap (E ⊗[F] B) (Localization.Away re)).comp
      (quadraticRelativeCoordinateHom E (E ⊗[F] B)
        (fun j => (1 : E) ⊗ₜ[F] g j) d a c)).Etale)
    (hgood : HasTensorGoodQuadraticNeighborhood F E B g d I a c P0 r)
    (hnative : HasQuadraticRetainedNativeChart K E (E ⊗[F] B) hfin hsep d
      (relativeCoordinateAlgHom E (E ⊗[F] B) d
        (fun k => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
          (parameterTuple E σ (d + 1) (prependParameters E d a c) k).val)) xE re r)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (φ : E →+* Ω)
    (hxRat : xE ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[F] B))) = 𝟙 _)
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hLower : PolynomialTailIsomorphisms K Ω Q d) :
    (sameStageLocalizedInputs K F E B hfin hsep g d I a c P0 re r xE hxE hre he
      hgood hnative φ).LowerIsomorphism Q := by
  let G := sameStageLocalizedInputs K F E B hfin hsep g d I a c P0 re r xE hxE hre he
      hgood hnative φ
  let : Module.Finite K E := hfin
  let : Algebra.IsSeparable K E := hsep
  let : IsAffine (SmoothSite.mk G.tail).left :=
    inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin d) E))))
  have hs := sameStageLocalizedInputs_tailResidue_separable K F E B hfin hsep
    g d I a c P0 re r xE hxE hre he hgood hnative φ hxRat
  apply G.lowerIsomorphism_of_structural_iso Q
  exact hLower E G.η hs

end QuadraticIncidence.InfinityChart
