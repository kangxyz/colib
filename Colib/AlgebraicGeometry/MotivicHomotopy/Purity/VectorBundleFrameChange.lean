/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.VectorBundleBasisChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.LinearFrameChange
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapSections

/-! # The coordinate matrix of a change of vector-bundle frames -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules)
  (V : X.affineOpens) {c : ℕ}

set_option quotPrecheck false in
local notation "U" => (V.1 : X.Opens)
set_option quotPrecheck false in
local notation "T" => (U).toScheme
set_option quotPrecheck false in
local notation "R" => Γ(X, U)
set_option quotPrecheck false in
local notation "P" => CommRingCat.of (MvPolynomial (Fin c) R)

variable (b b' : Module.Basis (Fin c) Γ(X, (V.1 : X.Opens)) Γ(E, (V.1 : X.Opens)))

/-- The rows of the frame change express the second basis in the first basis. -/
def vectorBundleFrameChangeMatrix :
    (Matrix (ULift.{u} (Fin c)) (ULift.{u} (Fin c)) Γ(T, ⊤))ˣ := by
  let v := b.reindex (Equiv.ulift.symm : Fin c ≃ ULift.{u} (Fin c))
  let v' := b'.reindex (Equiv.ulift.symm : Fin c ≃ ULift.{u} (Fin c))
  let r := (U).topIso.inv.hom
  exact
    { val := ((v.toMatrix v')ᵀ).map r
      inv := ((v'.toMatrix v)ᵀ).map r
      val_inv := by
        rw [← Matrix.map_mul, ← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
          Matrix.transpose_one, Matrix.map_one r (map_zero r) (map_one r)]
      inv_val := by
        rw [← Matrix.map_mul, ← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
          Matrix.transpose_one, Matrix.map_one r (map_zero r) (map_one r)] }

/-- The matrix entries are the basis coordinates transported to the affine open. -/
theorem vectorBundleFrameChangeMatrix_apply (i j : ULift.{u} (Fin c)) :
    (vectorBundleFrameChangeMatrix E V b b').val i j =
      (U).topIso.inv (b.repr (b' i.down) j.down) := by
  simp [vectorBundleFrameChangeMatrix, Module.Basis.toMatrix_apply]

variable [E.IsQuasicoherent]

private theorem frameChangePolynomial_X (j : Fin c) :
    Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E V.2 b
      ((Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E V.2 b').symm
        (MvPolynomial.X j)) =
      ∑ i, MvPolynomial.C (b.repr (b' j) i) * MvPolynomial.X i := by
  change SymmetricAlgebra.equivMvPolynomial b
      ((Stacks.SymAlgSections.symSectionsRingEquiv E V.2).symm
        ((Stacks.SymAlgSections.symSectionsRingEquiv E V.2)
          ((SymmetricAlgebra.equivMvPolynomial b').symm (MvPolynomial.X j)))) = _
  rw [RingEquiv.symm_apply_apply, SymmetricAlgebra.equivMvPolynomial_symm_X]
  conv_lhs => rw [← b.sum_repr (b' j)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(SymmetricAlgebra.ι R Γ(E, U)).map_smul]
  exact ((SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv.map_smul
    (b.repr (b' j) i) (SymmetricAlgebra.ι R Γ(E, U) (b i))).trans (by
      change (b.repr (b' j) i) •
        (SymmetricAlgebra.equivMvPolynomial b) (SymmetricAlgebra.ι R Γ(E, U) (b i)) = _
      rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, Algebra.smul_def,
        MvPolynomial.algebraMap_eq])

set_option quotPrecheck false in
local notation "e" => AffineSpace.isoSpecFinOfIso c (show IsAffineOpen U from V.2).isoSpec
set_option quotPrecheck false in
local notation "ψ" => Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E V.2

private theorem frameChangeIso_appTop_coord (j : ULift.{u} (Fin c)) :
    (e).inv.appTop (AffineSpace.coord T j) = (Scheme.ΓSpecIso P).inv (MvPolynomial.X j.down) := by
  simp only [AffineSpace.isoSpecFinOfIso, Iso.trans_inv, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  simp [AffineSpace.mvPolynomialFinUliftIso, MvPolynomial.renameEquiv_symm]

private theorem frameChangeIso_appTop_coeff (a : R) :
    (e).inv.appTop ((AffineSpace (ULift.{u} (Fin c)) T ↘ T).appTop ((U).topIso.inv a)) =
      (Scheme.ΓSpecIso P).inv (MvPolynomial.C a) := by
  let w := (show IsAffineOpen U from V.2).isoSpec
  have ha : w.inv.appTop ((U).topIso.inv a) = (Scheme.ΓSpecIso R).inv a := by
    have he : (U).topIso.inv ≫ w.inv.appTop = (Scheme.ΓSpecIso R).inv := by
      rw [IsAffineOpen.isoSpec_inv_appTop, Iso.inv_hom_id_assoc]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) a
  have hp : (e).inv ≫ (AffineSpace (ULift.{u} (Fin c)) T ↘ T) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin c) R)) ≫ w.inv :=
    AffineSpace.isoSpecFinOfIso_inv_over c (show IsAffineOpen U from V.2).isoSpec
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hp,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin c) R))).appTop
    (w.inv.appTop ((U).topIso.inv a)) = _
  rw [ha]
  let C : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map C).appTop) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

set_option maxHeartbeats 1200000 in
-- The coordinates require unfolding the relative-spectrum chart and its ring isomorphisms.
set_option synthInstance.maxHeartbeats 200000 in
-- The global sections and polynomial algebras carry induced instances.
/-- The transition between two charts on the same affine open is the literal matrix map. -/
theorem vectorBundleBasisChart_frameChange :
    (vectorBundleBasisChart E V b).inv ≫ (vectorBundleBasisChart E V b').hom =
      AffineSpace.matrixMap (vectorBundleFrameChangeMatrix E V b b').val := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, vectorBundleBasisChart_hom_over, AffineSpace.matrixMap_over]
    rw [← vectorBundleBasisChart_hom_over E V b]
    exact (vectorBundleBasisChart E V b).inv_hom_id_assoc _
  · intro j
    apply (ConcreteCategory.mono_iff_injective_of_preservesPullback (e).inv.appTop).1
      inferInstance
    let φ : P ⟶ P := CommRingCat.ofHom (((ψ) b').symm.trans ((ψ) b)).toRingHom
    have hcomp : (e).inv ≫ (vectorBundleBasisChart E V b).inv ≫
        (vectorBundleBasisChart E V b').hom = Spec.map φ ≫ (e).inv := by
      simp only [vectorBundleBasisChart, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
      change Spec.map (CommRingCat.ofHom ((ψ) b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((ψ) b').symm.toRingHom) ≫ (e).inv = _
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcomp,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, frameChangeIso_appTop_coord,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso P).inv
        ((ψ) b (((ψ) b').symm (MvPolynomial.X j.down))) =
      (e).inv.appTop
        ((AffineSpace.matrixMap (vectorBundleFrameChangeMatrix E V b b').val).appTop
          (AffineSpace.coord T j))
    rw [frameChangePolynomial_X, AffineSpace.matrixMap_appTop_coord]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
      vectorBundleFrameChangeMatrix_apply]
    rw [← Equiv.ulift.sum_comp (fun i : Fin c =>
      (Scheme.ΓSpecIso P).inv (MvPolynomial.C (b.repr (b' j.down) i)) *
        (Scheme.ΓSpecIso P).inv (MvPolynomial.X i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [frameChangeIso_appTop_coeff, frameChangeIso_appTop_coord]
    rfl

section Restrict

variable {V} {W : X.affineOpens} (h : W.1 ≤ V.1)

/-- The frame on the smaller affine open together with its generator equations. -/
def vectorBundleBasisRestrictData :
    { d : Module.Basis (Fin c) Γ(X, (W.1 : X.Opens)) Γ(E, (W.1 : X.Opens)) //
      ∀ i, d i = E.presheaf.map (homOfLE h).op (b i) } := by
  let r := (X.presheaf.map (homOfLE h).op).hom
  let : Algebra Γ(X, (V.1 : X.Opens)) Γ(X, (W.1 : X.Opens)) := r.toAlgebra
  let : Module Γ(X, (V.1 : X.Opens)) Γ(E, (W.1 : X.Opens)) := Module.compHom _ r
  let : IsScalarTower Γ(X, (V.1 : X.Opens)) Γ(X, (W.1 : X.Opens)) Γ(E, (W.1 : X.Opens)) :=
    ⟨fun x y z => mul_smul (r x) y z⟩
  let ρ : Γ(E, (V.1 : X.Opens)) →ₗ[Γ(X, (V.1 : X.Opens))] Γ(E, (W.1 : X.Opens)) :=
    { toFun := fun a => E.presheaf.map (homOfLE h).op a
      map_add' := fun a d => map_add _ a d
      map_smul' := fun a d => Scheme.Modules.map_smul E (homOfLE h) a d }
  have hρ : IsBaseChange Γ(X, (W.1 : X.Opens)) ρ :=
    isBaseChange_restrict_of_isAffineOpen E V.2 W.2 h (fun _ => rfl) ρ (fun _ => rfl)
  exact ⟨hρ.basis b, hρ.basis_apply b⟩

include b h in
/-- A frame over an affine open restricts to a frame over a smaller affine open. -/
def vectorBundleBasisRestrict :
    Module.Basis (Fin c) Γ(X, (W.1 : X.Opens)) Γ(E, (W.1 : X.Opens)) :=
  (vectorBundleBasisRestrictData E b h).val

/-- The restricted frame consists of the original restricted sections. -/
theorem vectorBundleBasisRestrict_apply (i : Fin c) :
    vectorBundleBasisRestrict E b h i = E.presheaf.map (homOfLE h).op (b i) :=
  (vectorBundleBasisRestrictData E b h).property i

set_option maxHeartbeats 1200000 in
-- The affine section comparison reduces through the graded and ungraded sheaf restrictions.
private theorem frameRestrict_generator (j : Fin c) :
    (symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op
        ((Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E V.2 b).symm
          (MvPolynomial.X j)) =
      (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E W.2
        (vectorBundleBasisRestrict E b h)).symm (MvPolynomial.X j) := by
  let a := homOfLE h
  let F := symmetricAlgebra X E
  let s := (symmetricAlgebraGen X E).val
  change F.ungradedSheaf.obj.map a.op
      (Stacks.SymAlgSections.symSectionsRingEquiv E V.2
        ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X j))) =
    Stacks.SymAlgSections.symSectionsRingEquiv E W.2
      ((SymmetricAlgebra.equivMvPolynomial (vectorBundleBasisRestrict E b h)).symm
        (MvPolynomial.X j))
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X, SymmetricAlgebra.equivMvPolynomial_symm_X,
    Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl,
    Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl,
    vectorBundleBasisRestrict_apply]
  change (F.ungradedSheaf.obj.map a.op).hom (F.ungradedIncl 1 (s.app (op V.1) (b j))) =
    F.ungradedIncl 1 (s.app (op W.1) (E.presheaf.map a.op (b j)))
  rw [F.ungradedIncl_naturality]
  congr 1
  exact (PresheafOfModules.naturality_apply s a.op (b j)).symm

set_option maxHeartbeats 1200000 in
-- The proof compares the two relative-spectrum charts and the restrictions of their coordinates.
/-- The affine chart of a restricted frame is the original chart restricted on the base. -/
@[reassoc]
theorem vectorBundleBasisChart_restrict :
    (vectorBundle X E).homOfLE (show
        vectorBundleToBase X E ⁻¹ᵁ (W.1 : X.Opens) ≤
          vectorBundleToBase X E ⁻¹ᵁ (V.1 : X.Opens) from
          (vectorBundleToBase X E).preimage_mono h) ≫
      (vectorBundleBasisChart E V b).hom =
    (vectorBundleBasisChart E W (vectorBundleBasisRestrict E b h)).hom ≫
      AffineSpace.map (ULift.{u} (Fin c)) (X.homOfLE h) := by
  let π := vectorBundleToBase X E
  let G := Stacks.RelativeSpec.gluedSpectrum (vectorBundleSituation X E)
  let h' : π ⁻¹ᵁ W.1 ≤ π ⁻¹ᵁ V.1 := π.preimage_mono h
  let m := (vectorBundle X E).homOfLE h'
  let φ := (symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op
  let cW := G.chartIsoPreimage W
  let cV := G.chartIsoPreimage V
  have hm : cW.hom ≫ m = Spec.map φ ≫ cV.hom := by
    apply (cancel_mono (π ⁻¹ᵁ V.1).ι).1
    rw [Category.assoc, Scheme.homOfLE_ι, Category.assoc]
    have hv : cV.hom ≫ (π ⁻¹ᵁ V.1).ι = G.chart V := G.chartIsoPreimage_hom_ι V
    have hw : cW.hom ≫ (π ⁻¹ᵁ W.1).ι = G.chart W := G.chartIsoPreimage_hom_ι W
    rw [hv, hw]
    exact (G.chart_naturality h).symm
  apply (cancel_epi cW.hom).1
  apply AffineSpace.hom_ext
  · let β := X.homOfLE h
    have hp : m ≫ π ∣_ V.1 = (π ∣_ W.1) ≫ β := by
      apply (cancel_mono V.1.ι).1
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι,
        Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
    simp only [Category.assoc, AffineSpace.map_over, vectorBundleBasisChart_hom_over,
      vectorBundleBasisChart_hom_over_assoc]
    rw [hp]
  · intro j
    let ψV := Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E V.2 b
    let ψW := Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E W.2
      (vectorBundleBasisRestrict E b h)
    let eV := AffineSpace.isoSpecFinOfIso c V.2.isoSpec
    let eW := AffineSpace.isoSpecFinOfIso c W.2.isoSpec
    have hV : cV.hom ≫ (vectorBundleBasisChart E V b).hom =
        Spec.map (CommRingCat.ofHom ψV.symm.toRingHom) ≫ eV.inv :=
      cV.hom_inv_id_assoc _
    have hW : cW.hom ≫ (vectorBundleBasisChart E W (vectorBundleBasisRestrict E b h)).hom =
        Spec.map (CommRingCat.ofHom ψW.symm.toRingHom) ≫ eW.inv :=
      cW.hom_inv_id_assoc _
    change ((cW.hom ≫ m ≫ (vectorBundleBasisChart E V b).hom).appTop (AffineSpace.coord _ j)) =
      ((cW.hom ≫ (vectorBundleBasisChart E W (vectorBundleBasisRestrict E b h)).hom ≫
        AffineSpace.map (ULift.{u} (Fin c)) (X.homOfLE h)).appTop (AffineSpace.coord _ j))
    rw [← Category.assoc cW.hom m, hm, Category.assoc, hV,
      ← Category.assoc cW.hom, hW]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
    rw [frameChangeIso_appTop_coord V j, frameChangeIso_appTop_coord W j]
    have natural {A B : CommRingCat.{u}} (ρ : A ⟶ B) (x : A) :
        (Spec.map ρ).appTop ((Scheme.ΓSpecIso A).inv x) = (Scheme.ΓSpecIso B).inv (ρ x) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality ρ).symm) x
    let AV := (symmetricAlgebraSheaf X E).right.obj.obj (op V.1)
    let AW := (symmetricAlgebraSheaf X E).right.obj.obj (op W.1)
    let PV := CommRingCat.of (MvPolynomial (Fin c) Γ(X, (V.1 : X.Opens)))
    let PW := CommRingCat.of (MvPolynomial (Fin c) Γ(X, (W.1 : X.Opens)))
    let v : PV ⟶ AV := @CommRingCat.ofHom PV AV inferInstance inferInstance ψV.symm.toRingHom
    let w : PW ⟶ AW := @CommRingCat.ofHom PW AW inferInstance inferInstance ψW.symm.toRingHom
    change (Spec.map φ).appTop ((Spec.map v).appTop
      ((Scheme.ΓSpecIso PV).inv (MvPolynomial.X j.down))) =
      (Spec.map w).appTop ((Scheme.ΓSpecIso PW).inv (MvPolynomial.X j.down))
    rw [natural v, natural w, natural φ]
    exact congrArg (fun z : AW => (Scheme.ΓSpecIso AW).inv z)
      (frameRestrict_generator E b h j.down)

end Restrict

end AlgebraicGeometry.Scheme.Modules
