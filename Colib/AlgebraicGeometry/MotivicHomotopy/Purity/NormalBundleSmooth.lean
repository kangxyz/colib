/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.ConormalRank
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# The normal bundle of a smooth pair as a smooth-site object

For smooth schemes of relative dimensions `n` and `m`, the conormal sheaf
has rank `n - m`. Its associated vector bundle is smooth of that relative
dimension. The construction below uses the actual normal bundle and its
zero section, with the original morphisms to the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Conormal

universe u

namespace Stacks.Conormal

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ S)
  [IsImmersion i] [Smooth p] [Smooth (i ≫ p)] {n m : ℕ}

/-- The actual normal-bundle projection is smooth of the codimension of a pure smooth pair. -/
theorem smoothOfRelativeDimension_normalBundleToBase
    (hX : RelativeDimension p n) (hZ : RelativeDimension (i ≫ p) m) :
    SmoothOfRelativeDimension (n - m) (normalBundleToBase i) := by
  have := Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheafDegreeOne
    i p hX hZ
  exact Stacks.Chow.smoothOfRelativeDimension_of_isAffineSpaceBundle _ (n - m)
    (Stacks.Chow.isAffineSpaceBundle_vectorBundleToBase (conormalSheafDegreeOne i) (n - m))

/-- The total space of the normal bundle is smooth over the original base. -/
theorem smooth_normalBundleToBase_comp
    (hX : RelativeDimension p n) (hZ : RelativeDimension (i ≫ p) m) :
    Smooth (normalBundleToBase i ≫ (i ≫ p)) := by
  have := smoothOfRelativeDimension_normalBundleToBase i p hX hZ
  have : Smooth (normalBundleToBase i) :=
    SmoothOfRelativeDimension.smooth (n - m) (normalBundleToBase i)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The original normal-bundle projection is smooth even when its rank varies. -/
theorem smooth_normalBundleToBase_of_smooth (p : X ⟶ S) [Smooth p] [Smooth (i ≫ p)] :
    Smooth (normalBundleToBase i) := by
  let E := conormalSheafDegreeOne i
  have hE : Scheme.Modules.IsFiniteLocallyFree E :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).2
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (conormalDegreeOneIso i)
        (h := Stacks.ConormalSequenceRight.isFiniteLocallyFree_conormalSheaf_of_smooth i p))
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Smooth.{u}) (Q := RingHom.Smooth)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Smooth.{u})
    (f := normalBundleToBase i) ?_
  intro x
  obtain ⟨U, hxU, J, hJ, ⟨e⟩⟩ := hE x
  obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  have hr : Set.range hV.fromSpec.base ⊆ Set.range U.ι.base := by
    rw [← Scheme.Hom.coe_opensRange, hV.opensRange_fromSpec, Scheme.Opens.range_ι]
    exact hVU
  obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset
    U.ι hV.fromSpec E J hr e
  let : Finite J := hJ
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨b⟩ := (tilde_fixed_free_iff_basis Γ(Z, V) Γ(E, V) J).mp
    ⟨Stacks.Modules.tildeIsoRestrictFromSpec E hV ≪≫ e'⟩
  let r := Fintype.card J
  let β := b.reindex (Fintype.equivFin J)
  obtain ⟨e'', he''⟩ := Stacks.Chow.exists_iso_affineSpace_of_mvPolynomialSections
    (Scheme.Modules.symmetricAlgebraSheaf Z E) ⟨V, hV⟩ r
    (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E hV β)
    (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv_app E hV β)
  refine ⟨V, hxV, ?_⟩
  change Smooth (Stacks.AffineAlgebraEquivalence.relativeSpecToBase
    (Scheme.Modules.symmetricAlgebraSheaf Z E) ∣_ V)
  rw [← he'', MorphismProperty.cancel_left_of_respectsIso @Smooth.{u}]
  let q := (AffineSpace (ULift.{u} (Fin r)) V.toScheme ↘ V.toScheme)
  have : SmoothOfRelativeDimension r q := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver _ _
  exact SmoothOfRelativeDimension.smooth r q

end Stacks.Conormal

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {Z X : SmoothSite S} (i : Z ⟶ X)
  [IsImmersion i.left] {n m : ℕ}

/-- The canonical normal bundle of a smooth pair as an object of the smooth site. -/
def normalBundleOfSmooth : SmoothSite S := by
  have : Smooth (i.left ≫ X.hom) := by rw [MorphismProperty.Over.w i]; infer_instance
  have : Smooth (Stacks.Conormal.normalBundleToBase i.left) :=
    Stacks.Conormal.smooth_normalBundleToBase_of_smooth i.left X.hom
  exact mk (Stacks.Conormal.normalBundleToBase i.left ≫ Z.hom)

/-- Pure pairs use the same normal-bundle object. -/
abbrev normalBundle (_hX : RelativeDimension X.hom n) (_hZ : RelativeDimension Z.hom m) :
    SmoothSite S := normalBundleOfSmooth i

@[simp]
theorem normalBundle_left (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    (normalBundle i hX hZ).left = Stacks.Conormal.normalBundle i.left := rfl

@[simp]
theorem normalBundle_hom (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    (normalBundle i hX hZ).hom = Stacks.Conormal.normalBundleToBase i.left ≫ Z.hom := rfl

/-- The original normal-bundle projection as a map of the smooth site. -/
def normalBundleProjection (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    normalBundle i hX hZ ⟶ Z :=
  homMk (Stacks.Conormal.normalBundleToBase i.left) rfl

/-- The actual zero section of the normal bundle as a map of the smooth site. -/
def normalBundleZeroSectionOfSmooth : Z ⟶ normalBundleOfSmooth i :=
  homMk (Modules.vectorBundleZeroSection Z.left (conormalSheafDegreeOne i.left)) (by
    change Modules.vectorBundleZeroSection Z.left (conormalSheafDegreeOne i.left) ≫
      (Modules.vectorBundleToBase Z.left (conormalSheafDegreeOne i.left) ≫ Z.hom) = Z.hom
    rw [← Category.assoc, Modules.vectorBundleZeroSection_comp_vectorBundleToBase,
      Category.id_comp])

/-- The original zero section of the normal bundle is a closed immersion. -/
instance normalBundleZeroSectionOfSmooth_isClosedImmersion :
    IsClosedImmersion (normalBundleZeroSectionOfSmooth i).left :=
  Modules.isClosedImmersion_vectorBundleZeroSection Z.left (conormalSheafDegreeOne i.left)

/-- Pure pairs use the same zero section. -/
abbrev normalBundleZeroSection (_hX : RelativeDimension X.hom n)
    (_hZ : RelativeDimension Z.hom m) : Z ⟶ normalBundleOfSmooth i :=
  normalBundleZeroSectionOfSmooth i

/-- The normal-bundle zero section splits its projection in the smooth site. -/
@[reassoc (attr := simp)]
theorem normalBundleZeroSection_projection (hX : RelativeDimension X.hom n)
    (hZ : RelativeDimension Z.hom m) :
    normalBundleZeroSection i hX hZ ≫ normalBundleProjection i hX hZ = 𝟙 Z := by
  apply MorphismProperty.Over.Hom.ext
  exact Modules.vectorBundleZeroSection_comp_vectorBundleToBase Z.left
    (conormalSheafDegreeOne i.left)

end AlgebraicGeometry.Scheme.SmoothSite

end
