/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.GlobalParameter
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedSymmetricUniversal

/-!
# The fibre-one section of the extended-Rees deformation

Evaluation at `t = 1` sends a homogeneous section `a t^n` of the extended
Rees algebra to `a`. It gives a retraction of its structure algebra map,
hence a canonical closed section of the original deformation projection.
The construction uses the extended Rees algebra already chosen by Stacks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace Stacks.Deformation

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Evaluation at one on the homogeneous extended-Rees algebra of sections. -/
def extReesEvalOne (W : X.Opens) :
    (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W) →+* Γ(X, W) :=
  (LaurentPolynomial.eval₂ (RingHom.id _) (1 : Units Γ(X, W))).comp
    (extReesLaurent I W)

/-- Evaluation at one forgets the degree of a homogeneous section. -/
@[simp]
theorem extReesEvalOne_incl (W : X.Opens) (n : ℤ)
    (x : ((extReesGradedAlgebra I).piece n).val.obj (op W)) :
    extReesEvalOne I W ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl n x) =
      extReesAmbient I n W x := by
  simp [extReesEvalOne, extReesLaurent_incl]

/-- Evaluation at one commutes with restriction to an open subset. -/
theorem extReesEvalOne_restrict {W W' : X.Opens} (h : W' ≤ W)
    (x : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W)) :
    extReesEvalOne I W'
        ((extReesGradedAlgebra I).toPresheafGradedAlgebra.totalRestrict (homOfLE h).op x) =
      X.presheaf.map (homOfLE h).op (extReesEvalOne I W x) := by
  induction x using Stacks.GradedAlgebra.incl_induction with
  | zero => simp only [map_zero]
  | incl n x =>
      rw [Stacks.GradedAlgebra.totalRestrict_incl, extReesEvalOne_incl,
        extReesEvalOne_incl]
      exact extReesAmbient_restrict I n W' W h x
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Evaluation at one as a morphism from the presheaf extended-Rees algebra. -/
def extReesEvalOnePresheaf :
    ungradedCommPresheaf X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) ⟶
      X.presheaf where
  app W := @CommRingCat.ofHom _ _
    ((extReesGradedAlgebra I).toPresheafGradedAlgebra.commRingTotal
      (extReesGradedAlgebra_mul_comm I) W) _ (extReesEvalOne I W.unop)
  naturality W W' f := by
    have h : W'.unop ≤ W.unop := leOfHom f.unop
    obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
    exact CommRingCat.hom_ext (RingHom.ext (extReesEvalOne_restrict I h))

/-- Evaluation at one fixes the structure sheaf. -/
theorem structureMap_comp_extReesEvalOnePresheaf :
    ungradedCommStructureMap X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) ≫
      extReesEvalOnePresheaf I = 𝟙 X.presheaf := by
  refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  change extReesEvalOne I W.unop
      ((extReesGradedAlgebra I).toPresheafGradedAlgebra.structureMap W r) = r
  let r' : X.ringCatSheaf.obj.obj W := r
  change extReesEvalOne I W.unop
      (r' • (1 : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total W)) = r
  rw [Stacks.GradedAlgebra.one_eq_incl, ← Stacks.GradedAlgebra.incl_smul,
    extReesEvalOne_incl]
  exact (extReesAmbient_smul I 0 W.unop r' ((extReesOne I).eval W)).trans
    ((congrArg (Stacks.Blowup.ringSectionToGamma r' * ·)
      (extReesAmbient_extReesOne I W)).trans (mul_one _))

/-- Evaluation at one on the sheafification of the ungraded extended Rees presheaf. -/
def extReesEvalOneUngraded :
    ungradedAlgebraSheaf X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) ⟶
      Under.mk (𝟙 X.sheaf) :=
  (ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I) (Under.mk (𝟙 X.sheaf))).symm
      ⟨extReesEvalOnePresheaf I, structureMap_comp_extReesEvalOnePresheaf I⟩

private theorem extReesEvalOneUngraded_incl (W : X.Opens) (n : ℤ)
    (x : ((extReesGradedAlgebra I).piece n).val.obj (op W)) :
    ((extReesEvalOneUngraded I).right.hom.app (op W)).hom
        (ungradedAlgebraSheafIncl X (extReesGradedAlgebra I)
          (extReesGradedAlgebra_mul_comm I) n W x) =
      extReesAmbient I n W x := by
  have h : ungradedCommToSheaf X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) ≫
      (extReesEvalOneUngraded I).right.hom = extReesEvalOnePresheaf I :=
    congrArg Subtype.val
      ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra I)
        (extReesGradedAlgebra_mul_comm I) (Under.mk (𝟙 X.sheaf))).apply_symm_apply
          ⟨extReesEvalOnePresheaf I, structureMap_comp_extReesEvalOnePresheaf I⟩)
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h (op W))
    ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl n x)).trans
      (extReesEvalOne_incl I W n x)

/-- Evaluation at one as a morphism from the original extended-Rees algebra sheaf. -/
def extReesEvalOneAlgebraHom : extReesAlgebraSheaf I ⟶ Under.mk (𝟙 X.sheaf) :=
  (ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)).inv ≫ extReesEvalOneUngraded I

/-- Evaluation at one on the presheaves underlying the original algebra sheaf. -/
abbrev extReesEvalOneSheaf : (extReesAlgebraSheaf I).right.obj ⟶ X.presheaf :=
  (extReesEvalOneAlgebraHom I).right.hom

/-- The original structure map is a section of evaluation at one. -/
theorem hom_comp_extReesEvalOneSheaf :
    (extReesAlgebraSheaf I).hom.hom ≫ extReesEvalOneSheaf I = 𝟙 X.presheaf :=
  congrArg (fun f : X.sheaf ⟶ X.sheaf => f.hom) (Under.w (extReesEvalOneAlgebraHom I))

/-- Evaluation at one on a homogeneous section in the original algebra-sheaf realization. -/
theorem extReesEvalOneSheaf_app_incl (W : X.Opens) (n : ℤ)
    (x : ((extReesGradedAlgebra I).piece n).val.obj (op W)) :
    ((extReesEvalOneSheaf I).app (op W)).hom
        (((ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
          (extReesGradedAlgebra_mul_comm I)).hom.right.hom.app (op W)).hom
          (ungradedAlgebraSheafIncl X (extReesGradedAlgebra I)
            (extReesGradedAlgebra_mul_comm I) n W x)) =
      extReesAmbient I n W x := by
  let e := ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)
  have he (a) : (e.inv.right.hom.app (op W)).hom ((e.hom.right.hom.app (op W)).hom a) = a :=
    congrArg (fun f => (f.right.hom.app (op W)).hom a) e.hom_inv_id
  change ((extReesEvalOneUngraded I).right.hom.app (op W)).hom
      ((e.inv.right.hom.app (op W)).hom ((e.hom.right.hom.app (op W)).hom
        (ungradedAlgebraSheafIncl X (extReesGradedAlgebra I)
          (extReesGradedAlgebra_mul_comm I) n W x))) = _
  rw [he]
  exact extReesEvalOneUngraded_incl I W n x

/-- The original deformation parameter evaluates to one. -/
@[simp]
theorem extReesEvalOneSheaf_paramSectionOf (W : X.Opens) :
    ((extReesEvalOneSheaf I).app (op W)).hom (paramSectionOf I W) = 1 :=
  (extReesEvalOneSheaf_app_incl I W (-1) (paramPiece I W)).trans
    (extReesAmbient_paramPiece I W)

/-- The canonical fibre-one section of the extended-Rees deformation. -/
def deformationOneSection : X ⟶ deformationSpace I :=
  retractionSection (extReesSituation I) (extReesEvalOneSheaf I)
    (hom_comp_extReesEvalOneSheaf I)

/-- The fibre-one section splits the original deformation projection. -/
@[reassoc (attr := simp)]
theorem deformationOneSection_toBase :
    deformationOneSection I ≫ deformationSpaceToBase I = 𝟙 X :=
  retractionSection_comp_toBase (extReesSituation I) (extReesEvalOneSheaf I)
    (hom_comp_extReesEvalOneSheaf I)

/-- The canonical fibre-one section is a closed immersion. -/
instance isClosedImmersion_deformationOneSection :
    IsClosedImmersion (deformationOneSection I) :=
  isClosedImmersion_retractionSection (extReesSituation I) (extReesEvalOneSheaf I)
    (hom_comp_extReesEvalOneSheaf I)

/-- On an affine chart the fibre-one section is the spectrum of evaluation at one. -/
theorem ι_deformationOneSection (W : X.affineOpens) :
    W.1.ι ≫ deformationOneSection I =
      W.1.toSpecΓ ≫ Spec.map ((extReesEvalOneSheaf I).app (op W.1)) ≫
        (gluedSpectrum (extReesSituation I)).chart W :=
  ι_retractionSection (extReesSituation I) (extReesEvalOneSheaf I)
    (hom_comp_extReesEvalOneSheaf I) W

/-- Pulling a homogeneous chart function back along the actual fibre-one section
forgets its degree. -/
theorem deformationOneSection_appLE_chartIncl (W : X.affineOpens) (n : ℤ)
    (x : ((extReesGradedAlgebra I).piece n).val.obj (op W.1))
    (h : W.1 ≤ deformationOneSection I ⁻¹ᵁ (deformationSpaceToBase I ⁻¹ᵁ W.1)) :
    ((deformationOneSection I).appLE (deformationSpaceToBase I ⁻¹ᵁ W.1) W.1 h).hom
        (chartIncl I n W.1 x) = extReesAmbient I n W.1 x := by
  have hp := pairToHom_appLE
    (retractionPair (extReesSituation I) (extReesEvalOneSheaf I)
      (hom_comp_extReesEvalOneSheaf I)) W h
  exact (ConcreteCategory.congr_hom hp
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)).hom.right.hom.app (op W.1)).hom
        (ungradedAlgebraSheafIncl X (extReesGradedAlgebra I)
          (extReesGradedAlgebra_mul_comm I) n W.1 x))).trans
            (extReesEvalOneSheaf_app_incl I W.1 n x)

/-- The actual fibre-one section pulls the original parameter back to one on each chart. -/
theorem deformationOneSection_appLE_paramChartOf (W : X.affineOpens)
    (h : W.1 ≤ deformationOneSection I ⁻¹ᵁ (deformationSpaceToBase I ⁻¹ᵁ W.1)) :
    ((deformationOneSection I).appLE (deformationSpaceToBase I ⁻¹ᵁ W.1) W.1 h).hom
      (paramChartOf I W.1) = 1 :=
  (deformationOneSection_appLE_chartIncl I W (-1) (paramPiece I W.1) h).trans
    (extReesAmbient_paramPiece I W.1)

end Stacks.Deformation

namespace Stacks.Deformation

open Stacks.Conormal

section Immersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The defining ideal of the closed immersion into the coborder pulls back to zero. -/
theorem coborderIdeal_comap_liftCoborder :
    (coborderIdeal i).comap i.liftCoborder = ⊥ := by
  apply bot_unique
  change i.liftCoborder.ker.comap i.liftCoborder ≤ ⊥
  rw [← Scheme.IdealSheafData.map_bot]
  exact Scheme.IdealSheafData.comap_map_le (⊥ : Z.IdealSheafData) i.liftCoborder

/-- The canonical closed support map from the deformation of the zero ideal on the centre.
Identification of its source with the affine-line cylinder is a separate comparison. -/
def deformationSupportMap :
    deformationSpace (⊥ : Z.IdealSheafData) ⟶ deformationSpace (coborderIdeal i) :=
  deformationMap i.liftCoborder (coborderIdeal i) ⊥
    (coborderIdeal_comap_liftCoborder i).le

/-- The canonical support map is a closed immersion. -/
instance isClosedImmersion_deformationSupportMap :
    IsClosedImmersion (deformationSupportMap i) :=
  isClosedImmersion_deformationMap i.liftCoborder (coborderIdeal i) ⊥
    (coborderIdeal_comap_liftCoborder i).le (coborderIdeal_comap_liftCoborder i).symm

/-- The support map retains the original projection to the closed centre. -/
@[reassoc]
theorem deformationSupportMap_toBase :
    deformationSupportMap i ≫ deformationSpaceToBase (coborderIdeal i) =
      deformationSpaceToBase (⊥ : Z.IdealSheafData) ≫ i.liftCoborder :=
  deformationMap_toBase i.liftCoborder (coborderIdeal i) ⊥
    (coborderIdeal_comap_liftCoborder i).le

/-- The support map preserves the scheme-theoretic zero fibre of the original parameter. -/
theorem deformationSupportMap_comap_zeroScheme :
    (Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
      (Scheme.unitModule (deformationSpace (coborderIdeal i)))
      (paramGlobal (coborderIdeal i))).comap (deformationSupportMap i) =
    Stacks.Divisors.zeroScheme (deformationSpace (⊥ : Z.IdealSheafData))
      (Scheme.unitModule (deformationSpace (⊥ : Z.IdealSheafData)))
      (paramGlobal (⊥ : Z.IdealSheafData)) :=
  comap_zeroScheme_paramGlobal i.liftCoborder (coborderIdeal i) ⊥
    (coborderIdeal_comap_liftCoborder i).le

end Immersion

section Closed

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- For a closed immersion, the canonical coborder neighborhood is the entire ambient scheme. -/
theorem isIso_coborderRange_ι_of_isClosedImmersion : IsIso i.coborderRange.ι := by
  have h : i.coborderRange = ⊤ :=
    TopologicalSpace.Opens.ext i.isClosedEmbedding.isClosed_range.coborder_eq
  rw [h, ← Scheme.topIso_hom]
  infer_instance

/-- The actual ambient-scheme inclusion into the fibre at one for a closed pair. -/
def closedPairOneSection : X ⟶ deformationSpace (coborderIdeal i) :=
  have := isIso_coborderRange_ι_of_isClosedImmersion i
  inv i.coborderRange.ι ≫ deformationOneSection (coborderIdeal i)

/-- The fibre-one inclusion of a closed pair is a closed immersion. -/
instance isClosedImmersion_closedPairOneSection : IsClosedImmersion (closedPairOneSection i) := by
  have := isIso_coborderRange_ι_of_isClosedImmersion i
  dsimp [closedPairOneSection]
  infer_instance

/-- The fibre-one inclusion of a closed pair splits the original ambient projection. -/
@[reassoc (attr := simp)]
theorem closedPairOneSection_toAmbient :
    closedPairOneSection i ≫
      (deformationSpaceToBase (coborderIdeal i) ≫ i.coborderRange.ι) = 𝟙 X := by
  have := isIso_coborderRange_ι_of_isClosedImmersion i
  simp [closedPairOneSection, Category.assoc]

end Closed

end Stacks.Deformation

end
