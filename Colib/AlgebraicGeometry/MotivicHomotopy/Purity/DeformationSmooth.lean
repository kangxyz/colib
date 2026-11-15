/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.CoordinateChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.CoordinateModel
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.FlatPullback
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OneSection
import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ChartGeneration
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateSubspace
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smoothness of the original deformation space of a smooth closed pair

The inverse image of the open complement of the centre is the deformation of
the unit ideal, where the original parameter is invertible. Along the centre,
the actual coordinate charts of a smooth closed pair give étale pullbacks of
the polynomial deformation. These opens cover the original deformation space.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.Conormal Stacks.MoreMorphisms
open MvPolynomial

universe u

namespace Stacks.Deformation

private theorem chartLaurent_bijective_of_ideal_eq_top {X : Scheme.{u}}
    (I : X.IdealSheafData) (W : X.affineOpens) (hI : I.ideal W = ⊤) :
    Function.Bijective (chartLaurent I W) := by
  constructor
  · exact (extReesLaurent_injective I W.1).comp
      (RingEquiv.ofBijective (chartRingHom I W.1) (bijective_chartRingHom I W)).symm.injective
  · intro l
    induction l using LaurentPolynomial.induction_on' with
    | add a b ha hb =>
        obtain ⟨a', ha'⟩ := ha
        obtain ⟨b', hb'⟩ := hb
        exact ⟨a' + b', by rw [map_add, ha', hb']⟩
    | C_mul_T n a =>
        have hm : a ∈ I.ideal W ^ n.toNat := by
          simp only [hI, Ideal.top_pow, Submodule.mem_top]
        let x := extReesOfMemZ I W n a hm
        refine ⟨chartIncl I n W.1 x, ?_⟩
        rw [← chartRingHom_incl, chartLaurent_chartRingHom, extReesLaurent_incl,
          extReesAmbient_extReesOfMemZ]

private theorem smooth_specMap_laurentConstants (R : CommRingCat.{u}) :
    Smooth (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))) := by
  let j := Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  let : IsOpenImmersion j := by
    have h := IsOpenImmersion.of_isLocalization (R := Polynomial R) (S := LaurentPolynomial R)
      (Polynomial.X : Polynomial R)
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R))))
    convert h using 3
  let : Smooth p := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    let hp : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
    exact RingHom.smooth_algebraMap.mpr hp
  have h : Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R)) =
      j ≫ p := by
    dsimp only [j, p]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (Polynomial.toLaurent_C r).symm
  rw [h]
  infer_instance

private theorem smooth_restrict_deformationSpaceToBase_top {X : Scheme.{u}}
    (W : X.affineOpens) :
    Smooth (deformationSpaceToBase (⊤ : X.IdealSheafData) ∣_ W.1) := by
  let I : X.IdealSheafData := ⊤
  let f := deformationSpaceToBase I
  let V := f ⁻¹ᵁ W.1
  let g := f ∣_ W.1
  let : IsAffine V := Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) W
  let R := Γ(X, W.1)
  let d := RingEquiv.ofBijective (chartLaurent I W)
    (chartLaurent_bijective_of_ideal_eq_top I W (congrFun Scheme.IdealSheafData.ideal_top W))
  let a := W.1.topIso
  let b := V.topIso
  let c : R ⟶ CommRingCat.of (LaurentPolynomial R) := CommRingCat.ofHom LaurentPolynomial.C
  have hc : RingHom.Smooth c.hom :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).1 (smooth_specMap_laurentConstants R)
  have hd : (f.app W.1 ≫ d.toCommRingCatIso.hom).hom = c.hom :=
    RingHom.ext (chartLaurent_app I W)
  have hf : (f.app W.1).hom.Smooth := by
    have hs : (f.app W.1 ≫ d.toCommRingCatIso.hom).hom.Smooth := hd.symm ▸ hc
    exact (RingHom.Smooth.respectsIso.cancel_right_isIso (f.app W.1)
      d.toCommRingCatIso.hom).mp hs
  have hsq : a.hom ≫ f.app W.1 = g.appTop ≫ b.hom := by
    have h := (arrowResLEAppIso f W.1 V le_rfl).hom.w
    change a.hom ≫ f.appLE W.1 V le_rfl =
      (f.resLE W.1 V le_rfl).appTop ≫ b.hom at h
    rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at h
    exact h
  have hg : g.appTop = a.hom ≫ f.app W.1 ≫ b.inv := by
    rw [← Category.assoc, hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := g)).2
  rw [hg, CommRingCat.hom_comp]
  exact (RingHom.Smooth.respectsIso.cancel_left_isIso a.hom (f.app W.1 ≫ b.inv)).mpr
    (by rw [CommRingCat.hom_comp]
        exact (RingHom.Smooth.respectsIso.cancel_right_isIso (f.app W.1) b.inv).mpr hf)

set_option backward.isDefEq.respectTransparency false in
/-- The original deformation of the unit ideal is smooth over its base. -/
theorem smooth_deformationSpaceToBase_top (X : Scheme.{u}) :
    Smooth (deformationSpaceToBase (⊤ : X.IdealSheafData)) := by
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Smooth.{u}) (Q := RingHom.Smooth)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Smooth.{u}) _
    (iSup_affineOpens_eq_top X) (smooth_restrict_deformationSpaceToBase_top (X := X))

private theorem comap_ker_of_pullback {Z Z' X X' : Scheme.{u}}
    {i : Z ⟶ X} {j : Z' ⟶ X'} {a : X' ⟶ X} {b : Z' ⟶ Z}
    [IsClosedImmersion i] (sq : IsPullback j b a i) :
    i.ker.comap a = j.ker := by
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

private theorem smooth_deformation_preimageOpen {X S : Scheme.{u}} (I : X.IdealSheafData)
    (p : X ⟶ S) (U : X.Opens)
    (h : Smooth (deformationSpaceToBase (I.comap U.ι) ≫ (U.ι ≫ p))) :
    Smooth ((deformationSpaceToBase I ⁻¹ᵁ U).ι ≫ (deformationSpaceToBase I ≫ p)) := by
  let f := deformationSpaceToBase I
  let e := deformationSpaceFlatPullbackIso U.ι I ≪≫ pullbackRestrictIsoRestrict f U
  have hπ : e.hom ≫ (f ∣_ U) = deformationSpaceToBase (I.comap U.ι) := by
    change ((deformationSpaceFlatPullbackIso U.ι I).hom ≫
      (pullbackRestrictIsoRestrict f U).hom) ≫ (f ∣_ U) = _
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict,
      deformationSpaceFlatPullbackIso_hom_snd]
  let a := (f ⁻¹ᵁ U).ι ≫ (f ≫ p)
  have ha : e.hom ≫ a = deformationSpaceToBase (I.comap U.ι) ≫ (U.ι ≫ p) := by
    dsimp only [a]
    rw [← Category.assoc ((f ⁻¹ᵁ U).ι), ← morphismRestrict_ι, Category.assoc,
      ← Category.assoc e.hom, hπ]
  let : Smooth (e.hom ≫ a) := ha.symm ▸ h
  have hcancel : e.inv ≫ e.hom ≫ a = a := Iso.inv_hom_id_assoc e a
  change Smooth a
  exact hcancel ▸ inferInstanceAs (Smooth (e.inv ≫ (e.hom ≫ a)))

private theorem smooth_deformation_preimageOpen_offCentre {X S : Scheme.{u}}
    (I : X.IdealSheafData) (p : X ⟶ S) [Smooth p] :
    Smooth ((deformationSpaceToBase I ⁻¹ᵁ I.support.compl).ι ≫
      (deformationSpaceToBase I ≫ p)) := by
  let U : X.Opens := I.support.compl
  have hI : I.comap U.ι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    exact ⟨fun hx => (show ¬ Scheme.Opens.ι U x ∈ I.support from x.2) hx, False.elim⟩
  apply smooth_deformation_preimageOpen I p U
  rw [hI]
  let : Smooth (deformationSpaceToBase (⊤ : U.toScheme.IdealSheafData)) :=
    smooth_deformationSpaceToBase_top _
  infer_instance

private abbrev coordinateAmbientToBase (R : Type u) [CommRing R] (m n : ℕ) :
    Spec (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))

-- These affine comparison proofs follow StacksFrontier/AlgebraicGeometry/DeRham/
-- BlowupSmoothCentreFormsAffine.lean in the pinned Stacks library.
section AffineCoordinates

variable (T : Scheme.{u}) [IsAffine T]

/-- The spectra of two polynomial rings whose variables are matched by an equivalence. -/
@[expose] def specRenameIso {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    Spec (.of (MvPolynomial σ Γ(T, ⊤))) ≅ Spec (.of (MvPolynomial τ Γ(T, ⊤))) where
  hom := Spec.map
    (CommRingCat.ofHom (MvPolynomial.renameEquiv Γ(T, ⊤) e).symm.toRingEquiv.toRingHom)
  inv := Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv Γ(T, ⊤) e).toRingEquiv.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact RingHom.ext fun x => (MvPolynomial.renameEquiv Γ(T, ⊤) e).symm_apply_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact RingHom.ext fun x => (MvPolynomial.renameEquiv Γ(T, ⊤) e).apply_symm_apply x

/-- Relative affine `σ`-space over an affine base `T`, as the spectrum of a polynomial ring over
`Γ(T, ⊤)` in variables indexed by `τ`, matched with `σ` by `e : σ ≃ τ`. -/
@[expose] def affineSpaceIsoSpecRename {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    AffineSpace σ T ≅ Spec (.of (MvPolynomial τ Γ(T, ⊤))) :=
  AffineSpace.isoOfIsAffine _ T ≪≫ specRenameIso T e

/-- The inverse of `affineSpaceIsoSpecRename T e` is the spectrum of the renaming of variables
along `e`, followed by the inverse of `AffineSpace.isoOfIsAffine`. -/
private theorem affineSpaceIsoSpecRename_inv {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    (affineSpaceIsoSpecRename T e).inv =
      Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv Γ(T, ⊤) e).toRingEquiv.toRingHom) ≫
        (AffineSpace.isoOfIsAffine σ T).inv :=
  rfl

/-- The inverse of `affineSpaceIsoSpecRename T e`, followed by the structure morphism of
`𝔸(σ; T)`, is the spectrum of the constant-coefficient map `C`, followed by `T.isoSpec.inv`. -/
private theorem affineSpaceIsoSpecRename_inv_over {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    (affineSpaceIsoSpecRename T e).inv ≫ (𝔸(σ; T) ↘ T) =
      Spec.map (CommRingCat.ofHom (C : Γ(T, ⊤) →+* MvPolynomial τ Γ(T, ⊤))) ≫
        T.isoSpec.inv := by
  rw [affineSpaceIsoSpecRename_inv, Category.assoc, AffineSpace.isoOfIsAffine_inv_over,
    ← Spec.map_comp_assoc]
  congr 2
  ext r
  simp

/-- `Spec.map φ` pulls the global section `ΓSpecIso.inv a` back to `ΓSpecIso.inv (φ a)`. -/
private theorem appTop_spec_map_ΓSpecIso_inv {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (φ a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- The inverse of `affineSpaceIsoSpecRename T e` pulls the coordinate function `k` of
`𝔸(σ; T)` back to the global section `X (e k)` of the spectrum of the polynomial ring. -/
private theorem affineSpaceIsoSpecRename_inv_appTop_coord {σ : Type u} {τ : Type}
    (e : σ ≃ τ) (k : σ) :
    (affineSpaceIsoSpecRename T e).inv.appTop (AffineSpace.coord T k) =
      (Scheme.ΓSpecIso (.of (MvPolynomial τ Γ(T, ⊤)))).inv (X (e k)) := by
  rw [affineSpaceIsoSpecRename_inv, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.comp_apply, AffineSpace.isoOfIsAffine_inv_appTop_coord]
  rw [appTop_spec_map_ΓSpecIso_inv]
  congr 1
  simp

/-- **Over an affine base the coordinate subspace of relative affine space is the coordinate
subspace of the spectrum of a polynomial ring.** -/
private theorem affineSpaceIsoSpecRename_inv_comp_coordinateSubspaceEmbedding (m n : ℕ) :
    (affineSpaceIsoSpecRename T (Equiv.ulift.{u} (α := Fin m))).inv ≫
        Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n =
      Stacks.MoreMorphisms.coordinateEmbedding Γ(T, ⊤) m n ≫
        (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
          ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).inv := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, show Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n ≫
      (𝔸(ULift.{u} (Fin (m + n)); T) ↘ T) =
        (𝔸(ULift.{u} (Fin m); T) ↘ T) from AffineSpace.homOfVector_over _ _,
      affineSpaceIsoSpecRename_inv_over, Category.assoc, affineSpaceIsoSpecRename_inv_over,
      Stacks.MoreMorphisms.coordinateEmbedding, ← Spec.map_comp_assoc]
    congr 2
    ext r
    simp [Stacks.MoreMorphisms.coordinateProjection]
  · rintro ⟨k⟩
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [Stacks.MoreMorphisms.coordinateEmbedding, affineSpaceIsoSpecRename_inv_appTop_coord,
      appTop_spec_map_ΓSpecIso_inv]
    induction k using Fin.addCases with
    | left j =>
      rw [Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_firstCoordinate,
        affineSpaceIsoSpecRename_inv_appTop_coord]
      congr 1
      simp [Stacks.MoreMorphisms.coordinateProjection]
    | right j =>
      rw [Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_lastCoordinate]
      simp [Stacks.MoreMorphisms.coordinateProjection]

/-- The identification of relative affine space with the spectrum of a polynomial ring lies over
the identification `T ≅ Spec Γ(T, ⊤)`. -/
theorem affineSpaceIsoSpecRename_hom_comp (m n : ℕ) :
    (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
      ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : Γ(T, ⊤) →+* MvPolynomial (Fin m ⊕ Fin n) Γ(T, ⊤))) =
      (𝔸(ULift.{u} (Fin (m + n)); T) ↘ T) ≫ T.isoSpec.hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc,
    show (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
          ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).inv ≫
        (𝔸(ULift.{u} (Fin (m + n)); T) ↘ T) = _ from
      affineSpaceIsoSpecRename_inv_over T _, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The coordinate situation over an affine base is the coordinate situation of Section 50.16**:
a cartesian square of isomorphisms over `T ≅ Spec Γ(T, ⊤)`. -/
theorem isPullback_coordinateSubspaceEmbedding_coordinateEmbedding (m n : ℕ) :
    IsPullback (affineSpaceIsoSpecRename T (Equiv.ulift.{u} (α := Fin m))).hom
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n)
      (Stacks.MoreMorphisms.coordinateEmbedding Γ(T, ⊤) m n)
      (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
        ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).hom := by
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [← cancel_epi (affineSpaceIsoSpecRename T (Equiv.ulift.{u} (α := Fin m))).inv,
    Iso.inv_hom_id_assoc, ← Category.assoc,
    affineSpaceIsoSpecRename_inv_comp_coordinateSubspaceEmbedding, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end AffineCoordinates

private theorem exists_smooth_deformation_preimageOpen {Z X S : Scheme.{u}}
    (i : Z ⟶ X) (p : X ⟶ S) [IsClosedImmersion i] [Smooth p] [Smooth (i ≫ p)] (z : Z) :
    ∃ U : X.Opens, i z ∈ U ∧
      Smooth ((deformationSpaceToBase i.ker ⁻¹ᵁ U).ι ≫
        (deformationSpaceToBase i.ker ≫ p)) := by
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show p (i z) ∈ (⊤ : S.Opens) from trivial)
  let X' := (p ⁻¹ᵁ W).toScheme
  let Z' := (i ⁻¹ᵁ (p ⁻¹ᵁ W)).toScheme
  let j : Z' ⟶ X' := i ∣_ (p ⁻¹ᵁ W)
  let p' : X' ⟶ W.toScheme := p ∣_ W
  let z' : Z' := ⟨z, hzW⟩
  let : IsAffine W.toScheme := hW
  let : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (i ∣_ (p ⁻¹ᵁ W)))
  let : Smooth p' := inferInstanceAs (Smooth (p ∣_ W))
  have hcomp : j ≫ p' = (i ≫ p) ∣_ W := by
    apply (cancel_mono W.ι).mp
    let a := (p ⁻¹ᵁ W).ι
    let b := (i ⁻¹ᵁ (p ⁻¹ᵁ W)).ι
    have h₁ : (j ≫ p') ≫ W.ι = j ≫ a ≫ p :=
      (Category.assoc _ _ _).trans (congrArg (j ≫ ·) (morphismRestrict_ι p W))
    have h₂ : j ≫ a ≫ p = b ≫ (i ≫ p) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ p) (morphismRestrict_ι i (p ⁻¹ᵁ W))).trans
          (Category.assoc _ _ _))
    have h₃ : b ≫ (i ≫ p) = ((i ≫ p) ∣_ W) ≫ W.ι :=
      (morphismRestrict_ι (i ≫ p) W).symm
    exact h₁.trans (h₂.trans h₃)
  let : Smooth (j ≫ p') :=
    hcomp.symm ▸ inferInstanceAs (Smooth ((i ≫ p) ∣_ W))
  obtain ⟨m, n, V, hzV, a, b, ha, hover, hpb⟩ :=
    Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback p' j z'
  let e := affineSpaceIsoSpecRename W.toScheme
    (Equiv.ulift.{u}.trans finSumFinEquiv.symm : ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n)
  let d := affineSpaceIsoSpecRename W.toScheme (Equiv.ulift.{u} (α := Fin m))
  let R : CommRingCat.{u} := Γ(W.toScheme, ⊤)
  let a' := a ≫ e.hom
  let b' := b ≫ d.hom
  let j' := j ∣_ V
  let I := coordinateIdeal R m n
  let : IsClosedImmersion (coordinateEmbedding R m n) :=
    coordinateEmbedding_isClosedImmersion R m n
  let hpull := isPullback_coordinateSubspaceEmbedding_coordinateEmbedding W.toScheme m n
  have hpb' : IsPullback j' b a (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding
      W.toScheme m n) := by
    unfold j'
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact hpb
  let hcart : IsPullback j' b' a' (coordinateEmbedding R m n) :=
    (hpb'.flip.paste_horiz hpull).flip
  have hmodel : I.comap a' = j'.ker :=
    comap_ker_of_pullback hcart
  let : Etale a := ha
  let : Etale a' := inferInstanceAs (Etale (a ≫ e.hom))
  let q := coordinateAmbientToBase R m n
  let : Smooth (deformationSpaceToBase I ≫ q) := smooth_coordinateDeformation R m n
  have hs := smooth_deformationSpaceToBase_comp_of_etale a' I q
  have hab : a' ≫ q = V.ι ≫ p' ≫ W.toScheme.isoSpec.hom := by
    change (a ≫ e.hom) ≫ q = _
    rw [Category.assoc, affineSpaceIsoSpecRename_hom_comp, ← Category.assoc]
    exact (congrArg (· ≫ W.toScheme.isoSpec.hom) hover).trans (Category.assoc _ _ _)
  have hs' : Smooth (deformationSpaceToBase j'.ker ≫
      (V.ι ≫ p' ≫ W.toScheme.isoSpec.hom)) := by
    rw [hmodel, hab] at hs
    exact hs
  have hs'' : Smooth (deformationSpaceToBase j'.ker ≫ (V.ι ≫ p')) := by
    let g := deformationSpaceToBase j'.ker ≫ (V.ι ≫ p')
    let w := W.toScheme.isoSpec
    have hg : g ≫ w.hom = deformationSpaceToBase j'.ker ≫
        (V.ι ≫ p' ≫ W.toScheme.isoSpec.hom) := by
      change (deformationSpaceToBase j'.ker ≫ (V.ι ≫ p')) ≫ w.hom = _
      rw [Category.assoc, Category.assoc]
    let : Smooth (g ≫ w.hom) := hg.symm ▸ hs'
    have hcancel : (g ≫ w.hom) ≫ w.inv = g := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (show Smooth g from hcancel ▸ inferInstanceAs (Smooth ((g ≫ w.hom) ≫ w.inv)))
  let r := V.ι ≫ (p ⁻¹ᵁ W).ι
  let : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion (V.ι ≫ (p ⁻¹ᵁ W).ι))
  let U : X.Opens := r.opensRange
  let t : V.toScheme ≅ U.toScheme := r.isoOpensRange
  have ht : t.hom ≫ U.ι = r := r.isoOpensRange_hom_ι
  have hU : i z ∈ U := by
    change i z ∈ Set.range r
    refine ⟨⟨j z', hzV⟩, ?_⟩
    change (p ⁻¹ᵁ W).ι (j z') = i z
    exact congrArg (fun f : Z' ⟶ X => f z') (morphismRestrict_ι i (p ⁻¹ᵁ W))
  have hker : i.ker.comap r = j'.ker := by
    rw [Scheme.IdealSheafData.comap_comp, comap_ker_of_pullback
      (isPullback_morphismRestrict i (p ⁻¹ᵁ W)), comap_ker_of_pullback
      (isPullback_morphismRestrict j V)]
  have hrp : r ≫ p = V.ι ≫ (p' ≫ W.ι) := by
    change (V.ι ≫ (p ⁻¹ᵁ W).ι) ≫ p = _
    rw [Category.assoc, ← morphismRestrict_ι]
  have hsV : Smooth (deformationSpaceToBase (i.ker.comap r) ≫ (r ≫ p)) := by
    rw [hker, hrp, ← Category.assoc V.ι, ← Category.assoc]
    let : Smooth (deformationSpaceToBase j'.ker ≫ V.ι ≫ p') := hs''
    infer_instance
  let J := i.ker.comap U.ι
  let f := deformationSpaceToBase J
  let u := (deformationSpaceFlatPullbackIso t.hom J).hom ≫ pullback.fst f t.hom
  have hu : IsIso u := inferInstanceAs (IsIso
    ((deformationSpaceFlatPullbackIso t.hom J).hom ≫ pullback.fst f t.hom))
  have huπ : u ≫ f = deformationSpaceToBase (J.comap t.hom) ≫ t.hom := by
    change ((deformationSpaceFlatPullbackIso t.hom J).hom ≫ pullback.fst f t.hom) ≫ f = _
    rw [Category.assoc, pullback.condition, deformationSpaceFlatPullbackIso_hom_snd_assoc]
  have hJ : J.comap t.hom = i.ker.comap r := by
    change (i.ker.comap U.ι).comap t.hom = _
    rw [← Scheme.IdealSheafData.comap_comp, ht]
  have hUSmooth : Smooth (f ≫ (U.ι ≫ p)) := by
    let g := f ≫ (U.ι ≫ p)
    let : Smooth (u ≫ g) := by
      change Smooth (u ≫ f ≫ U.ι ≫ p)
      rw [← Category.assoc u, huπ, Category.assoc, ← Category.assoc t.hom, ht, hJ]
      exact hsV
    have hcancel : inv u ≫ u ≫ g = g := IsIso.inv_hom_id_assoc u g
    exact (show Smooth g from hcancel ▸ inferInstanceAs (Smooth (inv u ≫ (u ≫ g))))
  exact ⟨U, hU, smooth_deformation_preimageOpen i.ker p U hUSmooth⟩

/-- The original extended-Rees deformation of the kernel of a smooth closed
immersion is smooth over the original base. -/
theorem smooth_deformationSpaceToBase_ker_comp {Z X S : Scheme.{u}}
    (i : Z ⟶ X) (p : X ⟶ S) [IsClosedImmersion i] [Smooth p] [Smooth (i ≫ p)] :
    Smooth (deformationSpaceToBase i.ker ≫ p) := by
  classical
  let f := deformationSpaceToBase i.ker
  let ι := {U : X.Opens // Smooth ((f ⁻¹ᵁ U).ι ≫ (f ≫ p))}
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun U : ι => f ⁻¹ᵁ U.1) ?_
    (fun U => U.2)
  apply eq_top_iff.mpr
  intro x _
  by_cases hx : f x ∈ i.ker.support
  · have hsupport : (i.ker.support : Set X) = Set.range i :=
      (Scheme.Hom.support_ker i).trans i.isClosedEmbedding.isClosed_range.closure_eq
    have hx' : f x ∈ Set.range i :=
      hsupport ▸ (show f x ∈ (i.ker.support : Set X) from hx)
    obtain ⟨z, hz⟩ := hx'
    obtain ⟨U, hU, hSmooth⟩ := exists_smooth_deformation_preimageOpen i p z
    exact Opens.mem_iSup.mpr ⟨⟨U, hSmooth⟩, by change f x ∈ U; rwa [← hz]⟩
  · exact Opens.mem_iSup.mpr
      ⟨⟨i.ker.support.compl, smooth_deformation_preimageOpen_offCentre i.ker p⟩, hx⟩

/-- The deformation of a smooth closed pair, on the original coborder model,
is smooth over its original base. -/
theorem smooth_deformationSpaceToBase_comp_of_isClosedImmersion {Z X S : Scheme.{u}}
    (i : Z ⟶ X) (p : X ⟶ S) [IsClosedImmersion i] [Smooth p] [Smooth (i ≫ p)] :
    Smooth (deformationSpaceToBase (coborderIdeal i) ≫ (i.coborderRange.ι ≫ p)) := by
  let : IsIso i.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i
  let : Smooth (deformationSpaceToBase i.ker ≫ p) :=
    smooth_deformationSpaceToBase_ker_comp i p
  have hpb : IsPullback i.liftCoborder (𝟙 Z) i.coborderRange.ι i :=
    IsPullback.of_vert_isIso ⟨(Scheme.Hom.liftCoborder_ι i).trans (Category.id_comp i).symm⟩
  have hI : i.ker.comap i.coborderRange.ι = coborderIdeal i :=
    comap_ker_of_pullback hpb
  rw [← hI]
  exact smooth_deformationSpaceToBase_comp_of_etale i.coborderRange.ι i.ker p

/-- The original deformation projection preserves separatedness after composing with
the base morphism of the pair. -/
theorem isSeparated_deformationSpaceToBase_comp {Z X S : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) [IsSeparated p] :
    IsSeparated (deformationSpaceToBase (coborderIdeal i) ≫ (i.coborderRange.ι ≫ p)) := by
  let : IsAffineHom (deformationSpaceToBase (coborderIdeal i)) :=
    isAffineHom_relativeSpecToBase (extReesAlgebraSheaf (coborderIdeal i))
  infer_instance

/-- For a closed pair over a quasicompact base morphism, the original deformation
space is quasicompact over the same base. -/
theorem quasiCompact_deformationSpaceToBase_comp_of_isClosedImmersion
    {Z X S : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ S) [IsClosedImmersion i] [QuasiCompact p] :
    QuasiCompact (deformationSpaceToBase (coborderIdeal i) ≫ (i.coborderRange.ι ≫ p)) := by
  let : IsIso i.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i
  let : IsAffineHom (deformationSpaceToBase (coborderIdeal i)) :=
    isAffineHom_relativeSpecToBase (extReesAlgebraSheaf (coborderIdeal i))
  infer_instance

end Stacks.Deformation
