/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.BoundaryFiniteFlat
public import Colib.AlgebraicGeometry.ProjectiveSpace.Sections.ClosedEmbedding
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# Prescribed boundary sections produce finite flat Cartier divisors

Serre lifting supplies the two global sections; the exact boundary frame equations then
supply their whole finite locally free Cartier zero schemes. The projective embedding and
noetherian coefficient ring are used for lifting. Properness of the structure map, an affine
base, and a quasi-affine complement smooth of relative dimension one supply the geometry.
These are additional geometric hypotheses, not consequences of a framed Picard root alone.

The frames in this theorem are specified on the entire original closed boundary, including
nilpotents. They remain inputs; the sections, their regularity and their finite flat zero
schemes are conclusions. No divisor or moving-relation certificate is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.Divisors

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring an invertible module by the pulled-back projective twist preserves invertibility.
No finiteness, noetherianity or regularity hypothesis is needed for this step. -/
instance isInvertible_pullbackTwistFunctor_obj
    (R : Type u) [CommRing R] (n : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Proj (polyGrading R n)) (d : ℤ) (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((pullbackTwistFunctor R n f d).obj M) := by
  have htwist : SheafOfModules.IsInvertible (Proj (polyGrading R n)).sheaf.obj
      (Proj (polyGrading R n)).ringCatSheaf.property (twistingSheaf (polyGrading R n) d) :=
    algebraicGeometry_isInvertible_twistingSheaf (polyGrading R n)
      (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading R n) d
  let H := (pullback f).obj (twistingSheaf (polyGrading R n) d)
  have hH : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property H :=
    pullback_isInvertible f _
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property H :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hH
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property M H)

/-- Actual simultaneous boundary-prescribed sections with finite locally free Cartier zero
schemes. The common Serre bound works for every supplied pair of full-boundary frames. -/
@[colib_tag "COL-1221"]
theorem exists_boundary_framed_finiteLocallyFree_section_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X Z U S : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (q : X ⟶ S) [IsProper q] (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      ∀ (eM : (pullback i).obj ((pullbackTwistFunctor R n f d).obj M) ≅
          SheafOfModules.unit Z.ringCatSheaf)
        (eN : (pullback i).obj ((pullbackTwistFunctor R n f d).obj N) ≅
          SheafOfModules.unit Z.ringCatSheaf),
      ∃ (a : Γ((pullbackTwistFunctor R n f d).obj M, ⊤))
        (b : Γ((pullbackTwistFunctor R n f d).obj N, ⊤)),
        Hom.app eM.hom ⊤ (pullbackGlobalSections i _ a) = (1 : Γ(Z, ⊤)) ∧
        Hom.app eN.hom ⊤ (pullbackGlobalSections i _ b) = (1 : Γ(Z, ⊤)) ∧
        IsRelativeEffectiveCartierDivisor q
          (zeroScheme X ((pullbackTwistFunctor R n f d).obj M) a) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme X ((pullbackTwistFunctor R n f d).obj M) a).subschemeι ≫ q) ∧
        Set.range (zeroScheme X ((pullbackTwistFunctor R n f d).obj M) a).subschemeι ⊆
          Set.range j ∧
        IsRelativeEffectiveCartierDivisor q
          (zeroScheme X ((pullbackTwistFunctor R n f d).obj N) b) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme X ((pullbackTwistFunctor R n f d).obj N) b).subschemeι ≫ q) ∧
        Set.range (zeroScheme X ((pullbackTwistFunctor R n f d).obj N) b).subschemeι ⊆
          Set.range j := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isClosedImmersion f
  have : M.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _ M hM
  have : N.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _ N hN
  obtain ⟨B, hB⟩ := exists_boundary_framed_section_pair R n f i M N
  refine ⟨B, fun d hd eM eN => ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hB d hd eM eN
  have hA := finiteLocallyFree_zeroScheme_of_boundary_frame q i j hcover _ a eM ha
  have hB := finiteLocallyFree_zeroScheme_of_boundary_frame q i j hcover _ b eN hb
  exact ⟨a, b, ha, hb, hA.1, hA.2.1,
    zeroScheme_range_subset_of_boundary_frame i j hcover _ a eM ha, hB.1, hB.2.1,
    zeroScheme_range_subset_of_boundary_frame i j hcover _ b eN hb⟩

end AlgebraicGeometry.Scheme.Modules
