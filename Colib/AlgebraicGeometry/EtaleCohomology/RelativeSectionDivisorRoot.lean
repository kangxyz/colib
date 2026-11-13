/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferenceBoundary
public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot
public import Colib.AlgebraicGeometry.EtaleCohomology.ClosedCurveDivisorRoot
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerPicardSpecialization

/-!
# Tensor roots of relative section-divisor differences

Over a strictly henselian local base, a proper smooth relative curve with a
closed fibre satisfying the native `IsCurve` condition has tensor roots of its
section-kernel differences for every positive invertible exponent.

The argument constructs the closed-fibre sections as actual pullback lifts,
uses their actual tensor root, and transports it by the relative divisor
pullback isomorphism. Proper Kummer specialization then gives a global root.
There is no input Picard-divisibility, degree, or fibre-root certificate, and no
assertion that the particular chosen fibre root extends.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.Kummer

/-- The signed difference of two actual sections has a global tensor root over a strictly
henselian local base. The closed fibre is explicitly required to be a curve in the native
sense; the geometric assumption is not inferred from relative dimension alone. -/
@[colib_tag "COL-1215", stacks 03RP
  "Closed-curve degree-zero tensor roots, transported by actual divisor pullback \
  and proper Kummer specialization",
  stacks 095T "Proper base change used by Kummer specialization to lift divisibility"]
theorem exists_schemeTensorPower_iso_relativeSectionKernel_differenceSheaf
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    [SmoothOfRelativeDimension 1 q]
    [IsCurve (IsLocalRing.ResidueField R) (closedFibreProjection R q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker) := by
  have hrel : SmoothOfRelativeDimension 1 (closedFibreProjection R q) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (isPullback_closedFibre R q) inferInstance
  have hsm : Smooth (closedFibreProjection R q) :=
    @SmoothOfRelativeDimension.smooth 1 _ _ (closedFibreProjection R q) hrel
  have hproper : IsProper (closedFibreProjection R q) := isProper_closedFibreProjection R q
  let s₀ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ closedFibre R q :=
    Scheme.baseChangedSection q (residueFieldPoint R) s hs
  let t₀ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ closedFibre R q :=
    Scheme.baseChangedSection q (residueFieldPoint R) t ht
  have hs₀ : s₀ ≫ closedFibreProjection R q = 𝟙 _ :=
    Scheme.baseChangedSection_snd q (residueFieldPoint R) s hs
  have ht₀ : t₀ ≫ closedFibreProjection R q = 𝟙 _ :=
    Scheme.baseChangedSection_snd q (residueFieldPoint R) t ht
  have hnκ : IsUnit (n : IsLocalRing.ResidueField R) := by
    simpa only [map_natCast] using hn.map (IsLocalRing.residue R)
  obtain ⟨M₀, hM₀, ⟨e₀⟩⟩ :=
    @exists_schemeTensorPower_iso_sectionKernel_differenceSheaf
      (IsLocalRing.ResidueField R) _ _ (closedFibre R q) (closedFibreProjection R q)
      inferInstance hsm hproper hrel s₀ t₀ hs₀ ht₀ n hnκ
  have := isEffectiveCartierDivisor_sectionKernel q s hs
  have := isEffectiveCartierDivisor_sectionKernel q t ht
  have hX : IsUnit (n : Γ(X, ⊤)) := by
    simpa only [map_natCast] using
      hn.map (((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom)
  let e : (Scheme.Modules.pullback (closedFibreInclusion R q)).obj
      (differenceSheaf s.ker t.ker) ≅ differenceSheaf s₀.ker t₀.ker :=
    sectionKernelDifferencePullbackIso q (residueFieldPoint R) s t hs ht
  exact exists_schemeTensorPower_iso_of_closedFibre R q hn0 hX
    (differenceSheaf s.ker t.ker) (isInvertible_differenceSheaf s.ker t.ker)
    M₀ hM₀ (e₀ ≪≫ e.symm)

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- Actual section kernels admit a global root and a frame on the full finite boundary,
compatible with the canonical trivialization away from their images. Neither a fibre root,
a boundary trivialization, nor an initial frame is supplied as input. -/
@[colib_tag "COL-1215", stacks 095T
  "Proper Kummer specialization of actual section-divisor roots \
  with compatible finite-boundary frame"]
theorem exists_relativeSectionKernel_root_compatible_frame
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    [SmoothOfRelativeDimension 1 q]
    [IsCurve (IsLocalRing.ResidueField R) (closedFibreProjection R q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (i : Spec (CommRingCat.of B) ⟶ X)
    (his : Disjoint (Set.range i) (Set.range s))
    (hit : Disjoint (Set.range i) (Set.range t))
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
      (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker),
      letI := hM
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible
          (Spec (CommRingCat.of B)).presheaf (ringSheafCond (Spec (CommRingCat.of B)))
          ((Scheme.Modules.pullback i).obj M) :=
        Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
          (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M)
      ∃ e : (Scheme.Modules.pullback i).obj M ≅
          _root_.SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
        tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
          structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n =
        (Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (n : ℤ)).symm ≪≫
          (Scheme.Modules.pullback i).mapIso α ≪≫
            sectionKernelDifferenceBoundaryIso q s t hs ht i his hit := by
  obtain ⟨M, hM, ⟨α⟩⟩ :=
    exists_schemeTensorPower_iso_relativeSectionKernel_differenceSheaf R q s t hs ht hn0 hn
  exact ⟨M, hM, α, exists_root_compatible_frame_of_module_finite R B i M
    (differenceSheaf s.ker t.ker) hM hn α
      (sectionKernelDifferenceBoundaryIso q s t hs ht i his hit)⟩

end Stacks.Kummer
