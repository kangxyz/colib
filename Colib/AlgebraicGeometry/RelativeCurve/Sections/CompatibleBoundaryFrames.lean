/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.PrescribedBoundary
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-!
# Compatible full-boundary frames for a divisor pair

A module-finite algebra over a local ring is semilocal, so every invertible module on its
spectrum has a frame. Applied to the auxiliary projective twist, this supplies the same frame
for both members of the divisor pair. The frame on the tensor with the given invertible
module is the tensor of its specified boundary frame with that auxiliary frame.

The original frame is an input, not existentially replaced. The second global section belongs
to the auxiliary twist itself, through the actual left unitor. Both zero schemes are the whole
native zero schemes and are proved finite locally free and Cartier. The given proper structure
map may have a different affine target from the ring used for the projective presentation.
No reducedness, perfectness, fibre integrality or henselianity is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.SheafOfModules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- An auxiliary invertible module has a frame on a module-finite affine boundary over a local
ring. No henselianity or tensor-power trivialization is required. -/
@[colib_tag "COL-1048",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/PicardUFD/Affine.lean:102-125" "ingredient"
    "Triviality of an invertible sheaf over a spectrum with trivial ring Picard group"]
theorem nonempty_frame_of_module_finite
    (R B : Type u) [CommRing R] [IsLocalRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B]
    (L : (Spec (CommRingCat.of B)).Modules)
    [hL : SheafOfModules.IsInvertible (Spec (CommRingCat.of B)).sheaf.obj
      (Spec (CommRingCat.of B)).ringCatSheaf.property L] :
    Nonempty (L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by
  let : Finite (MaximalSpectrum B) :=
    Stacks.RingTheory.SemilocalModuleFinite.finite_maximalSpectrum_of_moduleFinite_of_isLocalRing
      R B
  have : Stacks.SheafOfModules.IsInvertible (Spec (CommRingCat.of B)).presheaf
      (structureSheafRing (Spec (CommRingCat.of B)).toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  exact Stacks.PicardUFD.isTrivial_of_isInvertible_spec B L

/-- The product frame on the actual pullback of `M ⊗ H`, using the canonical pullback/tensor
comparison and the tensor of the two specified frames. -/
@[colib_tag "COL-1048"]
def pullbackTensorFrame {X Z : Scheme.{u}} (i : Z ⟶ X) (M H : X.Modules)
    (e : (pullback i).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eH : (pullback i).obj H ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (pullback i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj H) ≅
      SheafOfModules.unit Z.ringCatSheaf := by
  let c := (Stacks.RingedSpace.comparisonNatTrans i.toLRSHom.toShHom).app (M, H)
  have hc : IsIso c := Stacks.RingedSpace.comparisonNatTrans_app_isIso _ _
  exact @asIso _ _ _ _ c hc ≪≫ tensorProductIso Z.sheaf.obj Z.ringCatSheaf.property e eH ≪≫
    tensorProductLeftUnitor Z.sheaf.obj Z.ringCatSheaf.property
      (SheafOfModules.unit Z.ringCatSheaf)

/-- The native left unitor identifies the twist of the unit module with the auxiliary twist. -/
def pullbackTwistUnitIso (R : Type u) [CommRing R] (n : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Proj (polyGrading R n)) (d : ℤ) :
    (pullbackTwistFunctor R n f d).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      (pullback f).obj (twistingSheaf (polyGrading R n) d) :=
  tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property _

/-- Every pulled-back projective twist is invertible, by native degree-one generation. -/
instance isInvertible_pullbackProjectiveTwist
    (R : Type u) [CommRing R] (n : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Proj (polyGrading R n)) (d : ℤ) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((pullback f).obj (twistingSheaf (polyGrading R n) d)) := by
  have : SheafOfModules.IsInvertible (Proj (polyGrading R n)).sheaf.obj
      (Proj (polyGrading R n)).ringCatSheaf.property (twistingSheaf (polyGrading R n) d) :=
    algebraicGeometry_isInvertible_twistingSheaf (polyGrading R n)
      (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading R n) d
  exact Stacks.Divisors.pullback_isInvertible f _

/-- A specified frame of `M` on the full finite boundary determines compatible divisor-pair
frames. Only the frame of the auxiliary twist is chosen; the second section belongs to that
twist itself through the native left unitor. -/
@[colib_tag "COL-1048"]
theorem exists_compatible_boundary_framed_divisor_pair
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (n : ℕ)
    {X U S : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (q : X ⟶ S) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : (pullback i).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    ∃ C : ℤ, ∀ d : ℤ, C ≤ d →
      let H := (pullback f).obj (twistingSheaf (polyGrading R n) d)
      ∃ eH : (pullback i).obj H ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      ∃ (a : Γ((pullbackTwistFunctor R n f d).obj M, ⊤)) (b : Γ(H, ⊤)),
        Hom.app (pullbackTensorFrame i M H e eH).hom ⊤ (pullbackGlobalSections i _ a) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Hom.app eH.hom ⊤ (pullbackGlobalSections i H b) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor q
          (Stacks.Divisors.zeroScheme X ((pullbackTwistFunctor R n f d).obj M) a) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((Stacks.Divisors.zeroScheme X ((pullbackTwistFunctor R n f d).obj M) a).subschemeι ≫ q) ∧
        Set.range (Stacks.Divisors.zeroScheme X
          ((pullbackTwistFunctor R n f d).obj M) a).subschemeι ⊆ Set.range j ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor q (Stacks.Divisors.zeroScheme X H b) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((Stacks.Divisors.zeroScheme X H b).subschemeι ≫ q) ∧
        Set.range (Stacks.Divisors.zeroScheme X H b).subschemeι ⊆ Set.range j := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isInvertible_unit X.sheaf.obj X.ringCatSheaf.property
  obtain ⟨C, hC⟩ := exists_boundary_framed_finiteLocallyFree_section_pair R n f q i j hcover
    M (SheafOfModules.unit X.ringCatSheaf)
  refine ⟨C, fun d hd => ?_⟩
  let H := (pullback f).obj (twistingSheaf (polyGrading R n) d)
  obtain ⟨eH⟩ := nonempty_frame_of_module_finite R B ((pullback i).obj H)
  let uH := pullbackTwistUnitIso R n f d
  let eA := pullbackTensorFrame i M H e eH
  let eB := (pullback i).mapIso uH ≪≫ eH
  obtain ⟨a, b', ha, hb', hA, hAfin, hArange, -, -, -⟩ := hC d hd eA eB
  let b := Hom.app uH.hom ⊤ b'
  have hb : Hom.app eH.hom ⊤ (pullbackGlobalSections i H b) =
      (1 : Γ(Spec (CommRingCat.of B), ⊤)) := by
    have hnat := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      i uH.hom b'
    exact (congrArg (fun t => Hom.app eH.hom ⊤ t) hnat).trans hb'
  have hB := finiteLocallyFree_zeroScheme_of_boundary_frame q i j hcover H b eH hb
  exact ⟨eH, a, b, ha, hb, hA, hAfin, hArange, hB.1, hB.2.1,
    zeroScheme_range_subset_of_boundary_frame i j hcover H b eH hb⟩

end AlgebraicGeometry.Scheme.Modules
