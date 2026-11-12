/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SameFibreDifference
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard
public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerPicardSpecialization

/-!
# Framed roots of sections with the same closed-fibre morphism

The compactification is only required to be proper. Smooth relative dimension one
is assumed on an open containing the two section images, not on the whole scheme.
Equality of the closed-fibre morphisms makes the actual pulled-back difference
trivial, so the unit module supplies its tensor root. Proper Kummer specialization
then yields a global root. The finite-algebra frame correction works on the entire
boundary, including its nilpotents.

This route uses no smooth-proper curve, Jacobian, degree-zero divisibility,
normality, Noetherianity, or supplied Cartier/root/comparison certificate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.Kummer

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The difference of two sections in a smooth curve open has a global tensor root
when their closed-fibre morphisms agree. The whole proper scheme need not be smooth. -/
@[colib_tag "COL-1055", stacks 095T
  "Proper Kummer specialization of the unit root for equal closed-fibre sections"]
theorem exists_schemeTensorPower_iso_sameFibreSectionKernel_differenceSheaf
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X U : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : residueFieldPoint R ≫ s = residueFieldPoint R ≫ t)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker) := by
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j s hs hsj
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j t ht htj
  have hX : IsUnit (n : Γ(X, ⊤)) := by
    simpa only [map_natCast] using
      hn.map (((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom)
  let M₀ : (closedFibre R q).Modules :=
    _root_.SheafOfModules.unit (closedFibre R q).ringCatSheaf
  have hM₀ : Stacks.SheafOfModules.IsInvertible (closedFibre R q).presheaf
      (closedFibre R q).ringCatIsSheaf M₀ :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  let e : (Scheme.Modules.pullback (closedFibreInclusion R q)).obj
      (differenceSheaf s.ker t.ker) ≅ M₀ :=
    sectionKernelDifferencePullbackUnitIsoOfRangeSubset q (residueFieldPoint R)
      j s t hs ht hsj htj hst
  let e₀ : Stacks.SheafOfModules.schemeTensorPower (closedFibre R q) M₀ hM₀ (n : ℤ) ≅
      (Scheme.Modules.pullback (closedFibreInclusion R q)).obj
        (differenceSheaf s.ker t.ker) :=
    structureSheafTensorPowerIso (closedFibre R q) n ≪≫ e.symm
  exact exists_schemeTensorPower_iso_of_closedFibre R q hn0 hX
    (differenceSheaf s.ker t.ker) (isInvertible_differenceSheaf s.ker t.ker) M₀ hM₀ e₀

/-- The root and its compatible frame are constructed on the full module-finite
boundary. No frame, fibre root, Cartier witness, or Picard-divisibility input is required. -/
@[colib_tag "COL-1055"]
theorem exists_sameFibreSectionKernel_root_compatible_frame
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X U : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : residueFieldPoint R ≫ s = residueFieldPoint R ≫ t)
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
            sectionKernelDifferenceBoundaryIsoOfRangeSubset q j s t hs ht hsj htj i his hit := by
  obtain ⟨M, hM, ⟨α⟩⟩ :=
    exists_schemeTensorPower_iso_sameFibreSectionKernel_differenceSheaf
      R q j s t hs ht hsj htj hst hn0 hn
  exact ⟨M, hM, α, exists_root_compatible_frame_of_module_finite R B i M
    (differenceSheaf s.ker t.ker) hM hn α
      (sectionKernelDifferenceBoundaryIsoOfRangeSubset q j s t hs ht hsj htj i his hit)⟩

end Stacks.Kummer
