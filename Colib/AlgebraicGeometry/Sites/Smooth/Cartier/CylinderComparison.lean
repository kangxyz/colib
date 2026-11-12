/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.SmoothEtaleComparisonOverBase
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
Adapted from https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cartier/CylinderComparison.lean
Source blob 960d6a7a73bbe07e80da702bac79fcc9fa3f7cab; the target uses the existing native
contraction cylinder.

# Actual smooth-site Cartier cylinder charts

The native comparison uses the affine line as the first pullback factor. The
canonical pullback symmetry transports it to the literal cylinder used by
contraction. Both full closed-fiber squares and the ground-field maps are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]

/-- Exchange the literal polynomial factors and use the fixed native cylinder comparison. -/
def nativeCylinderIso (D : SmoothSite (Spec (.of k))) :
    Scheme.Hom.cylinder k D.hom ≅ (Contraction.affineLineCylinder.obj D).left :=
  pullbackSymmetry _ _ ≪≫
    (forgetScheme (Spec (.of k))).mapIso
      (Contraction.affineCylinderPolynomialIso (.of k) D).symm

/-- The literal factor exchange retains the original polynomial zero map. -/
theorem cylinderZeroSection_symmetry (D : SmoothSite (Spec (.of k))) :
    Scheme.Hom.cylinderZeroSection k D.hom ≫ (pullbackSymmetry _ _).hom =
      (Contraction.polynomialAffineSection (.of k) D 0).left := by
  apply pullback.hom_ext
  · dsimp only [Scheme.Hom.cylinderZeroSection, Contraction.polynomialAffineSection,
      productLift, homMk]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd]
    exact (pullback.lift_fst _ _ _).symm
  · dsimp only [Scheme.Hom.cylinderZeroSection, Contraction.polynomialAffineSection,
      Contraction.toBase, Contraction.polynomialAffinePoint, productLift, homMk]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst]
    exact (pullback.lift_snd _ _ _).symm

/-- The comparison preserves the actual zero section as a morphism. -/
@[reassoc (attr := simp)]
theorem cylinderZeroSection_nativeCylinderIso (D : SmoothSite (Spec (.of k))) :
    Scheme.Hom.cylinderZeroSection k D.hom ≫ (nativeCylinderIso D).hom =
      (Contraction.nativeAffineSection (.of k) D 0).left := by
  have hz := congrArg (fun f => f.left)
    (Contraction.nativeAffineSection_polynomialIso (.of k) D 0)
  change (Contraction.nativeAffineSection (.of k) D 0).left ≫
    (Contraction.affineCylinderPolynomialIso (.of k) D).hom.left =
      (Contraction.polynomialAffineSection (.of k) D 0).left at hz
  have hz' := congrArg (fun f => f ≫
    (Contraction.affineCylinderPolynomialIso (.of k) D).inv.left) hz
  have he : (Contraction.affineCylinderPolynomialIso (.of k) D).hom.left ≫
      (Contraction.affineCylinderPolynomialIso (.of k) D).inv.left = 𝟙 _ :=
    congrArg (fun f => f.left) (Contraction.affineCylinderPolynomialIso (.of k) D).hom_inv_id
  simp only [Category.assoc, he, Category.comp_id] at hz'
  change Scheme.Hom.cylinderZeroSection k D.hom ≫ ((pullbackSymmetry _ _).hom ≫
    (Contraction.affineCylinderPolynomialIso (.of k) D).inv.left) = _
  rw [← Category.assoc, cylinderZeroSection_symmetry]
  exact hz'.symm

/-- The native cylinder comparison preserves the actual base projection. -/
@[reassoc]
theorem nativeCylinderIso_hom_projection (D : SmoothSite (Spec (.of k))) :
    (nativeCylinderIso D).hom ≫
      ((Contraction.projection (additiveGroupObject (Spec (.of k)))).app D).left =
      pullback.snd _ _ := by
  have h := Contraction.affineCylinderPolynomialIso_hom_projection (.of k) D
  have hi : (Contraction.affineCylinderPolynomialIso (.of k) D).inv ≫
      (Contraction.projection (additiveGroupObject (Spec (.of k)))).app D =
      productFst D (Contraction.polynomialAffineLine (.of k)) := by
    rw [← h, Iso.inv_hom_id_assoc]
  have hi' := congrArg (fun f => f.left) hi
  change (Contraction.affineCylinderPolynomialIso (.of k) D).inv.left ≫
    ((Contraction.projection (additiveGroupObject (Spec (.of k)))).app D).left =
      pullback.fst _ _ at hi'
  change ((pullbackSymmetry _ _).hom ≫
    (Contraction.affineCylinderPolynomialIso (.of k) D).inv.left) ≫
      ((Contraction.projection (additiveGroupObject (Spec (.of k)))).app D).left = _
  rw [Category.assoc, hi', pullbackSymmetry_hom_comp_fst]
  rfl

/-- An actual open of a smooth closed pair, with its original field structure. -/
def closedOpenSite {Y : SmoothSite (Spec (.of k))} {Z : Scheme.{u}}
    (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)] (O : Z.Opens) :
    SmoothSite (Spec (.of k)) := by
  let f : Z ⟶ Spec (.of k) := i ≫ Y.hom
  let : LocallyOfFiniteType f := inferInstanceAs (LocallyOfFiniteType (i ≫ Y.hom))
  let : QuasiCompact f := inferInstanceAs (QuasiCompact (i ≫ Y.hom))
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian Z := ⟨⟩
  exact mk (O.ι ≫ i ≫ Y.hom)

/-- Every point of an actual smooth Cartier pair has a common étale comparison
with its own literal contraction cylinder. The two squares retain the entire
original closed fiber; no perfect-field or supplied-chart hypothesis is used. -/
theorem exists_cartier_cylinder_comparison
    (Y : SmoothSite (Spec (.of k))) {Z : Scheme.{u}}
    (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor i.ker) (z : Z) :
    ∃ O : Z.Opens, z ∈ O ∧
      ∃ (V : SmoothSite (Spec (.of k))) (a : V ⟶ Y)
        (b : V ⟶ Contraction.affineLineCylinder.obj (closedOpenSite (Y := Y) i O))
        (d : closedOpenSite (Y := Y) i O ⟶ V),
        Etale a.left ∧ Etale b.left ∧
        IsPullback d.left O.ι a.left i ∧
        IsPullback d.left (𝟙 _) b.left
          (Contraction.nativeAffineSection (.of k) (closedOpenSite (Y := Y) i O) 0).left := by
  obtain ⟨U, hU, hz, V, a, b, d, ha, hb, hpa, hpb, _hia, _hib,
      hbase, hsa, hsb, hqa, hqb⟩ :=
    Scheme.exists_smooth_cartier_etale_cylinder_comparison_over_base i Y.hom hI z
  let : Etale a := ha
  let : Etale b := hb
  let : IsSeparated a := hsa
  let : IsSeparated b := hsb
  let : QuasiCompact a := hqa
  let : QuasiCompact b := hqb
  let : IsAffine U.toScheme := hU
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian
    (show Y.left ⟶ Spec (.of k) from Y.hom)
  let : QuasiCompact U.ι := quasiCompact_of_compactSpace U.ι
  let O := i ⁻¹ᵁ U
  let D := closedOpenSite (Y := Y) i O
  let T : SmoothSite (Spec (.of k)) := mk (a ≫ U.ι ≫ Y.hom)
  let a' : T ⟶ Y := homMk (a ≫ U.ι) (by
    change (a ≫ U.ι) ≫ Y.hom = a ≫ U.ι ≫ Y.hom
    exact Category.assoc _ _ _)
  let b' : T ⟶ Contraction.affineLineCylinder.obj D := homMk
    (b ≫ (nativeCylinderIso D).hom) (by
      change (b ≫ (nativeCylinderIso D).hom) ≫
        (((Contraction.projection (additiveGroupObject (Spec (.of k)))).app D).left ≫
          D.hom) = a ≫ U.ι ≫ Y.hom
      rw [Category.assoc, nativeCylinderIso_hom_projection_assoc]
      exact hbase.symm)
  let d' : D ⟶ T := homMk d (by
    change d ≫ a ≫ U.ι ≫ Y.hom = O.ι ≫ i ≫ Y.hom
    rw [← Category.assoc d a, hpa.w, Category.id_comp, morphismRestrict_ι_assoc])
  have hswap : IsPullback (Scheme.Hom.cylinderZeroSection k D.hom)
      (𝟙 (D.left)) (nativeCylinderIso D).hom
      (Contraction.nativeAffineSection (.of k) D 0).left := by
    let : IsIso (𝟙 D.left) := inferInstanceAs (IsIso (𝟙 (D.left : Scheme.{u})))
    exact IsPullback.of_vert_isIso
      ⟨(cylinderZeroSection_nativeCylinderIso D).trans (Category.id_comp _).symm⟩
  refine ⟨O, hz, T, a', b', d', ?_, ?_, ?_, ?_⟩
  · change Etale (a ≫ U.ι)
    infer_instance
  · change Etale (b ≫ (nativeCylinderIso D).hom)
    infer_instance
  · change IsPullback d (i ⁻¹ᵁ U).ι (a ≫ U.ι) i
    simpa only [Category.id_comp] using hpa.paste_vert (isPullback_morphismRestrict i U)
  · change IsPullback d (𝟙 (D.left)) (b ≫ (nativeCylinderIso D).hom)
      (Contraction.nativeAffineSection (.of k) D 0).left
    simpa only [Category.id_comp] using hpb.paste_vert hswap

end AlgebraicGeometry.Scheme.SmoothSite
