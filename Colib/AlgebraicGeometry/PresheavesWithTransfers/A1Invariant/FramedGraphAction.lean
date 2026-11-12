/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BoundaryUnitAction
public import Colib.AlgebraicGeometry.Correspondences.Divisors.GeometricFramedMovingRelation
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-!
# Original framed moving graphs act equally on ordinary HI torsion coefficients

The actual COL-1079 moving construction supplies its sections, finite locally free
zero schemes and original boundary-normalized rational correction internally. The
COL-1100 polynomial endpoints kill that correction on ordinary HI coefficients.

This wrapper retains COL-1079's local Noetherian coefficient ring and compatible
root/frame as inputs. It does not identify a strict henselization with an object of
`Sm(k)`. The imported lower principal and boundary-unit actions work on general
smooth affine integral bases without a local-ring hypothesis; descending the finite
root, frame, sections and geometry to such a stage is a separate task.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.Chow
open Stacks.SheafOfModules (schemeTensorPower)

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite
  PrincipalFamilyUnitOpen

attribute [local instance] framedCorrectionInvertible framedCorrectionQuasicoherent
  framedCorrectionDifferenceInvertible framedCorrectionDifferenceAGInvertible
  framedCorrectionPullbackInvertible framedCorrectionPullbackAGInvertible
  framedCorrectionMulCommutative framedCorrectionTensorEquivalence framedCorrectionPowerInvertible
  movingTensorQuotientSecondInvertible movingTensorQuotientTensorInvertible

/-- An actual framed tensor root and its compatible whole-boundary frame force equality
of the two original graph actions on ordinary HI torsion coefficients. All moving
sections and the original principal polynomial homotopy are produced internally. -/
@[colib_ref "motivic_source_3df0a472"
  "Motivic/Transfers/Presheaf/Actions/Principal/Family.lean:52-69"
  "adaptation"
  "original HI principal-action ingredient applied to the constructed framed graph relation; \
  local coefficient-ring hypotheses retained, not a full rigidity theorem",
  colib_tag "COL-1105"]
theorem transfer_geometric_framed_graph_eq
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Nonempty (Spec (CommRingCat.of B))] (n : ℕ)
    {X U : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    (g : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion g]
    (q : X ⟶ A.left) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (r : U ⟶ Limits.pullback A.hom T.hom) (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (σ τ : A.left ⟶ X) (hσ : σ ≫ q = 𝟙 A.left) (hτ : τ ≫ q = 𝟙 A.left)
    (σU τU : A.left ⟶ U) (hσU : σU ≫ j = σ) (hτU : τU ≫ j = τ)
    (hD : ∀ y : Spec (CommRingCat.of B), i y ∉ σ.ker.support)
    (hE : ∀ y : Spec (CommRingCat.of B), i y ∉ τ.ker.support)
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    let := sectionKernel_cartier_of_factor q j σ hσ σU hσU
    let := sectionKernel_cartier_of_factor q j τ hτ τU hτU
    ∀ (_hcompat : tensorPowerMap _ e (k + 1) ≪≫ structureSheafTensorPowerIso _ (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i σ.ker τ.ker hD hE),
    transfer P (graphCorrespondenceOfComponents A.hom T.hom
      (σU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
      (sectionTarget_base A.hom T.hom r σU
        (retainedSection_firstProjection A.hom T.hom q j r hr σ hσ σU hσU))
      (Cor.finite_genericPoints K ((Cor.graphFunctor K).obj A))) =
    transfer P (graphCorrespondenceOfComponents A.hom T.hom
      (τU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
      (sectionTarget_base A.hom T.hom r τU
        (retainedSection_firstProjection A.hom T.hom q j r hr τ hτ τU hτU))
      (Cor.finite_genericPoints K ((Cor.graphFunctor K).obj A))) := by
  dsimp only
  intro hcompat
  let : IsAffine ((𝟭 Scheme).obj A.left) := ‹IsAffine A.left›
  let : IsIntegral ((𝟭 Scheme).obj A.left) := ‹IsIntegral A.left›
  let : IsNoetherian A.left := inferInstance
  obtain ⟨c, hc⟩ := exists_geometric_framed_graph_moving_relation R B n g q i j hcover
    A.hom T.hom r hr σ τ hσ hτ σU τU hσU hτU hD hE L k α e hcompat
  obtain ⟨eH, a, b, ha0, hb0, hAfin, hBfin, haU, hbU, haB, hbB, Z, hrel, hZ, hbound⟩ :=
    hc c le_rfl
  let := hAfin
  let := hBfin
  let D₁ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr
      (zeroScheme X (tensorObj L ((pullback g).obj (twistingSheaf (polyGrading R n) c))) a) haU
  let D₂ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr
      (zeroScheme X ((pullback g).obj (twistingSheaf (polyGrading R n) c)) (b.eval (op ⊤))) hbU
  let Z₀ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T := Z
  change _ = (k + 1) • (D₁ - D₂) + Z₀ at hrel
  have hcov : (Set.range j)ᶜ ⊆ Set.range i := by
    intro x hx
    exact (hcover x).resolve_left hx
  let z := r ≫ Limits.pullback.snd A.hom T.hom
  have hz : j ≫ q ≫ A.hom = z ≫ T.hom := by
    rw [← Category.assoc, ← hr, Category.assoc, Limits.pullback.condition]
    simp only [z, Category.assoc]
  have hrz : retainedCurveMap A.hom T.hom q j z hz = r := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst (j ≫ q) z hz).trans hr.symm
    · exact Limits.pullback.lift_snd (j ≫ q) z hz
  have hzero := transfer_boundaryNormalized_rationalUnit_eq_zero P hP A T q j i hcov z hz
    _ hbound Z₀ (by
      change Z.val = _
      rw [hrz]
      exact hZ)
  let S₀ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    (graphCorrespondenceOfComponents A.hom T.hom
      (σU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
      (sectionTarget_base A.hom T.hom r σU
        (retainedSection_firstProjection A.hom T.hom q j r hr σ hσ σU hσU))
      (Cor.finite_genericPoints K ((Cor.graphFunctor K).obj A)))
  let T₀ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    (graphCorrespondenceOfComponents A.hom T.hom
      (τU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
      (sectionTarget_base A.hom T.hom r τU
        (retainedSection_firstProjection A.hom T.hom q j r hr τ hτ τU hτU))
      (Cor.finite_genericPoints K ((Cor.graphFunctor K).obj A)))
  change transfer P S₀ = transfer P T₀
  have hrel₀ : S₀ - T₀ = (k + 1) • (D₁ - D₂) + Z₀ := hrel
  apply sub_eq_zero.mp
  rw [← transfer_sub, hrel₀, transfer_add, hzero, add_zero]
  have hmul : transfer P ((k + 1) • (D₁ - D₂)) = (k + 1) • transfer P (D₁ - D₂) :=
    P.obj.map_nsmul
  rw [hmul]
  ext x
  exact hn _

end AlgebraicGeometry.PresheafWithTransfers
