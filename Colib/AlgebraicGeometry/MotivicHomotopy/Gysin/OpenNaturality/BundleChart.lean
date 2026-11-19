/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.VectorBundleBasisChart
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeNaturality
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapSections

/-! # Degree-one coordinates of the original vector-bundle charts -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

local notation "N" => vectorBundleOver X (F := F)

/-- A homogeneous linear function on the bundle is the value of its universal
module morphism on the given section of the defining module. -/
abbrev vectorBundleLinearFunction (U : X.Opens) (a : Γ(F, U)) :
    Γ((N).left, (N).hom ⁻¹ᵁ U) :=
  ((vectorBundleHomEquiv F N (𝟙 N)).val.app (op U)) a

private theorem vectorBundleLinearFunction_eq (V : X.affineOpens) (a : Γ(F, V.1)) :
    vectorBundleLinearFunction F V.1 a =
      ((universalAlgebraMap (vectorBundleSituation X F)).right.app (op V.1)).hom
        (Stacks.SymAlgSections.symSectionsRingEquiv F V.2
          (SymmetricAlgebra.ι Γ(X, V.1) Γ(F, V.1) a)) := by
  let A := symmetricAlgebra X F
  let hA := symmetricAlgebra_mul_comm X F
  let hsym := isSymmetricAlgebra_symmetricAlgebra X F
  let G := symmetricAlgebraGen X F
  let p := pushforwardAlgebra (N).hom
  let c := (symmetricAlgebraSheafComparison F).hom ≫ (vectorBundlePushforwardIso X).inv
  have h₀ : c ≫ pushforwardAlgebraMap (𝟙 N) = c :=
    (congrArg (c ≫ ·) (pushforwardAlgebraMap_id N)).trans (Category.comp_id c)
  have h₁ := congrArg (fun f : F ⟶ structurePushforward (N).hom => (f.val.app (op V.1)) a)
    (vectorBundleHomEquiv_apply F N (𝟙 N))
  have h₂ := congrArg (fun d => ((ungradedAlgebraSheafModuleHomEquiv A hA p G hsym
    d).val.app (op V.1)) a) h₀
  have h₃ := ungradedAlgebraSheafModuleHomEquiv_apply_val_app A hA p G hsym c V.1 a
  have h := ungradedToGradedRight_ungradedAlgebraSheafIncl X A hA 1 V.1 (G.val.app (op V.1) a)
  have hgen := Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl F V.2 a
  refine h₁.trans (h₂.trans (h₃.trans ?_))
  change ((universalAlgebraMap (vectorBundleSituation X F)).right.app (op V.1)).hom
    (((symmetricAlgebraSheafComparison F).hom.right.hom.app (op V.1)).hom
      (ungradedAlgebraSheafIncl X A hA 1 V.1 (G.val.app (op V.1) a))) = _
  exact congrArg _ (h.trans hgen.symm)

set_option maxHeartbeats 500000 in
-- Reduce the affine chart to the spectrum of the symmetric algebra on its selected basis.
/-- Pulling back an affine coordinate along the chosen basis chart gives the
actual linear function of the corresponding basis section. -/
theorem vectorBundleBasisChart_appTop_coord (V : X.affineOpens) {c : ℕ}
    (b : Module.Basis (Fin c) Γ(X, V.1) Γ(F, V.1)) (j : ULift.{u} (Fin c)) :
    (vectorBundleBasisChart F V b).hom.appTop (AffineSpace.coord V.1.toScheme j) =
      ((N).hom ⁻¹ᵁ V.1).topIso.inv (vectorBundleLinearFunction F V.1 (b j.down)) := by
  let A := (symmetricAlgebraSheaf X F).sections V.1
  let P := CommRingCat.of (MvPolynomial (Fin c) Γ(X, V.1))
  let e := AffineSpace.isoSpecFinOfIso c V.2.isoSpec
  let ψ := Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv F V.2 b
  let q := (gluedSpectrum (vectorBundleSituation X F)).chartIsoPreimage V
  have he : e.inv.appTop (AffineSpace.coord V.1.toScheme j) =
      (ΓSpecIso P).inv (MvPolynomial.X j.down) := by
    simp only [e, AffineSpace.isoSpecFinOfIso, Iso.trans_inv, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]
    rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    simp [AffineSpace.mvPolynomialFinUliftIso, MvPolynomial.renameEquiv_symm]
  let φ : P ⟶ A := ψ.toCommRingCatIso.inv
  have hφ : (Spec.map φ).appTop ((ΓSpecIso P).inv (MvPolynomial.X j.down)) =
      (ΓSpecIso A).inv (ψ.symm (MvPolynomial.X j.down)) := by
    rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have hb : ψ.symm (MvPolynomial.X j.down) =
      Stacks.SymAlgSections.symSectionsRingEquiv F V.2
        (SymmetricAlgebra.ι Γ(X, V.1) Γ(F, V.1) (b j.down)) := by
    change Stacks.SymAlgSections.symSectionsRingEquiv F V.2
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X j.down)) = _
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  have hU := universalAlgebraMap_app_comp_topIso_inv (vectorBundleSituation X F) V
  change (q.inv ≫ Spec.map φ ≫ e.inv).appTop (AffineSpace.coord V.1.toScheme j) = _
  have hl : (q.inv ≫ Spec.map φ ≫ e.inv).appTop (AffineSpace.coord V.1.toScheme j) =
      q.inv.appTop ((Spec.map φ).appTop (e.inv.appTop (AffineSpace.coord V.1.toScheme j))) := by
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rfl
  refine hl.trans ((congrArg (fun x => q.inv.appTop ((Spec.map φ).appTop x)) he).trans ?_)
  refine (congrArg (fun x => q.inv.appTop x) hφ).trans ?_
  refine (congrArg (fun x => q.inv.appTop ((ΓSpecIso A).inv x)) hb).trans ?_
  refine (ConcreteCategory.congr_hom hU _).symm.trans ?_
  exact congrArg (fun x => ((N).hom ⁻¹ᵁ V.1).topIso.inv x)
    (vectorBundleLinearFunction_eq F V (b j.down)).symm

/-- Evaluation of a bundle generator at a point of the bundle is restriction of
its universal linear function along that point. -/
theorem vectorBundleHomEquiv_appLE_linearFunction {W : Over X} (v : W ⟶ N)
    (U : X.Opens) (a : Γ(F, U))
    (h : W.hom ⁻¹ᵁ U ≤ v.left ⁻¹ᵁ ((N).hom ⁻¹ᵁ U)) :
    ((vectorBundleHomEquiv F W v).val.app (op U)) a =
      v.left.appLE ((N).hom ⁻¹ᵁ U) (W.hom ⁻¹ᵁ U) h (vectorBundleLinearFunction F U a) := by
  have hv := vectorBundleHomEquiv_comp F v (𝟙 N)
  rw [Category.comp_id] at hv
  have h' := congrArg (fun f : F ⟶ structurePushforward W.hom => (f.val.app (op U)) a) hv
  rw [comp_val_app_apply] at h'
  refine h'.trans ((AlgebraSheaf.underlyingModuleMap_val_app_apply
    (pushforwardAlgebraMap v) (op U) _).trans ?_)
  exact ConcreteCategory.congr_hom (pushforwardAlgebraMap_app v U h) _

end AlgebraicGeometry.Scheme.Modules
