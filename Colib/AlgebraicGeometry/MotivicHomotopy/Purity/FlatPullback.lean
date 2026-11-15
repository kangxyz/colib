/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.DeformationSpace
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesPullbackFlat
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.GradedRealizationPullbackIso
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNormalBundleIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChangeOverBase
import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafDegreewise

/-!
# Flat pullback of the extended-Rees algebra

The extended-Rees algebra has degree `n` piece `I ^ n.toNat`. The canonical
map on those powers therefore gives its pullback comparison in every integer
degree. Flatness makes every component invertible, and the ungraded
realization commutes with pullback. This identifies the actual algebra
sheaves used to construct deformation spaces.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open SheafOfModules.GradedAlgebra Stacks.Blowup Stacks.RelativeSpec
open Stacks.AffineAlgebraEquivalence Stacks.GradedRealizationPullback

universe u

namespace Stacks.Deformation

variable {Y X : Scheme.{u}} (g : Y ⟶ X) (I : X.IdealSheafData)

/-- Pullback on ambient sections of a homogeneous extended-Rees piece. -/
theorem extReesAmbient_reesPieceComap (n : ℤ) (W : X.Opens)
    (x : (extReesPiece I n).val.obj (op W)) :
    extReesAmbient (I.comap g) n (g ⁻¹ᵁ W)
        ((reesPieceComap g I (n.toNat : ℤ)).val.app (op W) x) =
      (g.app W).hom (extReesAmbient I n W x) :=
  reesPieceAmbient_comap g I (n.toNat : ℤ) W x

/-- The original pullback of powers, as a map of extended-Rees graded algebras. -/
def extReesComapUnitalHom :
    UnitalHom (extReesGradedAlgebra I)
      (Stacks.RingedSpace.pushforwardAlgebra g.toLRSHom.toShHom
        (extReesGradedAlgebra (I.comap g))) where
  app n := reesPieceComap g I (n.toNat : ℤ)
  map_mul n m W x y := by
    obtain ⟨W⟩ := W
    apply extReesAmbient_injective (I.comap g) (n + m) (g ⁻¹ᵁ W)
    let a := (reesPieceComap g I (n.toNat : ℤ)).val.app (op W) x
    let b := (reesPieceComap g I (m.toNat : ℤ)).val.app (op W) y
    let z := (extReesMul I n m).app (op W) x y
    change extReesAmbient (I.comap g) (n + m) (g ⁻¹ᵁ W)
        ((reesPieceComap g I ((n + m).toNat : ℤ)).val.app (op W) z) =
      extReesAmbient (I.comap g) (n + m) (g ⁻¹ᵁ W)
        ((extReesMul (I.comap g) n m).app (op (g ⁻¹ᵁ W)) a b)
    exact (extReesAmbient_reesPieceComap g I (n + m) W z).trans
      ((congrArg (g.app W).hom (extReesAmbient_extReesMul I n m W x y)).trans
        ((map_mul (g.app W).hom _ _).trans
          ((congrArg₂ (· * ·) (extReesAmbient_reesPieceComap g I n W x).symm
            (extReesAmbient_reesPieceComap g I m W y).symm).trans
              (extReesAmbient_extReesMul (I.comap g) n m (g ⁻¹ᵁ W) a b).symm)))
  map_one W := by
    obtain ⟨W⟩ := W
    apply extReesAmbient_injective (I.comap g) 0 (g ⁻¹ᵁ W)
    exact (extReesAmbient_reesPieceComap g I 0 W ((extReesOne I).eval (op W))).trans
      ((congrArg (g.app W).hom (extReesAmbient_extReesOne I (op W))).trans
        ((map_one (g.app W).hom).trans (extReesAmbient_extReesOne (I.comap g) _).symm))

/-- The adjoint comparison from the pullback extended-Rees algebra. -/
def extReesGradedPullbackHom :
    UnitalHom (Stacks.GradedRealizationPullback.pbGraded g (extReesGradedAlgebra I))
      (extReesGradedAlgebra (I.comap g)) :=
  Stacks.RingedSpace.transposeUnitalHom g.toLRSHom.toShHom (extReesComapUnitalHom g I)

/-- Degree `n` of the extended comparison is the original power comparison in degree
`n.toNat`. -/
theorem extReesGradedPullbackHom_app (n : ℤ) :
    (extReesGradedPullbackHom g I).app n =
      (reesGradedPullbackHom g I).app (n.toNat : ℤ) := by
  let f := g.toLRSHom.toShHom
  have he := Stacks.RingedSpace.transposeUnitalHom_app f (extReesComapUnitalHom g I) n
  have hr := Stacks.RingedSpace.transposeUnitalHom_app f (reesComapUnitalHom g I) (n.toNat : ℤ)
  exact he.trans (hr.symm)

/-- Flat pullback preserves every homogeneous piece of the extended-Rees algebra. -/
theorem isIso_extReesGradedPullbackHom_app [Flat g] (n : ℤ) :
    IsIso ((extReesGradedPullbackHom g I).app n) := by
  rw [extReesGradedPullbackHom_app]
  exact isIso_reesGradedPullbackHom_app g I (n.toNat : ℤ) (Int.natCast_nonneg _)

/-- The canonical algebra-sheaf comparison for the extended-Rees algebra. -/
def extReesAlgebraPullbackHom :
    (Stacks.AffineAlgebraEquivalence.algebraPullback g).obj (extReesAlgebraSheaf I) ⟶
      extReesAlgebraSheaf (I.comap g) :=
  (Stacks.GradedRealizationPullback.comparisonIso g (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)).hom ≫
      gradedAlgebraSheafMap Y (extReesGradedPullbackHom g I)
        (Stacks.GradedRealizationPullback.pbGraded_mul_comm g (extReesGradedAlgebra I)
          (extReesGradedAlgebra_mul_comm I)) (extReesGradedAlgebra_mul_comm (I.comap g))

/-- The extended-Rees algebra commutes with flat pullback. -/
theorem isIso_extReesAlgebraPullbackHom [Flat g] :
    IsIso (extReesAlgebraPullbackHom g I) := by
  let e := Stacks.GradedRealizationPullback.comparisonIso g (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)
  let f := gradedAlgebraSheafMap Y (extReesGradedPullbackHom g I)
    (Stacks.GradedRealizationPullback.pbGraded_mul_comm g (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)) (extReesGradedAlgebra_mul_comm (I.comap g))
  let : ∀ n, IsIso ((extReesGradedPullbackHom g I).app n) :=
    isIso_extReesGradedPullbackHom_app g I
  let : IsIso f := isIso_gradedAlgebraSheafMap Y _ _ _
  change IsIso (e.hom ≫ f)
  infer_instance

/-- The canonical flat-pullback isomorphism of the actual extended-Rees algebra sheaves. -/
def extReesAlgebraPullbackIso [Flat g] :
    (Stacks.AffineAlgebraEquivalence.algebraPullback g).obj (extReesAlgebraSheaf I) ≅
      extReesAlgebraSheaf (I.comap g) :=
  haveI := isIso_extReesAlgebraPullbackHom g I
  asIso (extReesAlgebraPullbackHom g I)

private def deformationSpaceFlatPullbackOverIso [Flat g] :
    Over.mk (deformationSpaceToBase (I.comap g)) ≅
      (Over.pullback g).obj (Over.mk (deformationSpaceToBase I)) :=
  (Stacks.AffineAlgebraEquivalence.relativeSpecOverIso
    (extReesAlgebraPullbackIso g I)).symm ≪≫
      (Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso g (extReesAlgebraSheaf I)).symm

/-- The actual extended-Rees deformation commutes with flat base change. -/
def deformationSpaceFlatPullbackIso [Flat g] :
    deformationSpace (I.comap g) ≅ pullback (deformationSpaceToBase I) g :=
  (Over.forget Y).mapIso (deformationSpaceFlatPullbackOverIso g I)

/-- The flat base-change isomorphism preserves the original projection to the source base. -/
@[reassoc (attr := simp)]
theorem deformationSpaceFlatPullbackIso_hom_snd [Flat g] :
    (deformationSpaceFlatPullbackIso g I).hom ≫ pullback.snd (deformationSpaceToBase I) g =
      deformationSpaceToBase (I.comap g) := by
  change (deformationSpaceFlatPullbackOverIso g I).hom.left ≫
    ((Over.pullback g).obj (Over.mk (deformationSpaceToBase I))).hom =
    (Over.mk (deformationSpaceToBase (I.comap g))).hom
  exact (deformationSpaceFlatPullbackOverIso g I).hom.w

/-- Under étale pullback, smoothness of the model deformation implies smoothness of its
base-changed deformation over the same base scheme. -/
theorem smooth_deformationSpaceToBase_comp_of_etale
    {S : Scheme.{u}} (p : X ⟶ S) [Etale g]
    [Smooth (deformationSpaceToBase I ≫ p)] :
    Smooth (deformationSpaceToBase (I.comap g) ≫ (g ≫ p)) := by
  have he : (deformationSpaceFlatPullbackIso g I).hom ≫
      pullback.fst (deformationSpaceToBase I) g ≫ (deformationSpaceToBase I ≫ p) =
      deformationSpaceToBase (I.comap g) ≫ (g ≫ p) := by
    rw [← Category.assoc (pullback.fst (deformationSpaceToBase I) g), pullback.condition,
      Category.assoc, ← Category.assoc (deformationSpaceFlatPullbackIso g I).hom,
      deformationSpaceFlatPullbackIso_hom_snd]
  rw [← he]
  infer_instance

private def deformationComapAlgebraHom :
    extReesAlgebraSheaf I ⟶ (algebraPushforward g).obj (extReesAlgebraSheaf (I.comap g)) :=
  (ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)).inv ≫
    deformationUngradedHom g I (I.comap g) le_rfl ≫
    (algebraPushforward g).map (ungradedAlgebraSheafIsoGradedAlgebraSheaf Y
      (extReesGradedAlgebra (I.comap g)) (extReesGradedAlgebra_mul_comm (I.comap g))).hom

private theorem deformationComapAlgebraHom_ungradedIncl (n : ℤ) (U : X.Opens)
    (x : ((extReesGradedAlgebra I).piece n).val.obj (op U)) :
    ((deformationComapAlgebraHom g I).right.hom.app (op U)).hom
        ((extReesGradedAlgebra I).ungradedIncl n x) =
      (extReesGradedAlgebra (I.comap g)).ungradedIncl n
        ((reesPieceComap g I (n.toNat : ℤ)).val.app (op U) x) := by
  let A := extReesGradedAlgebra I
  let B := extReesGradedAlgebra (I.comap g)
  let V := g ⁻¹ᵁ U
  let a := (ungradedAlgebraSheafIsoGradedAlgebraSheaf X A
    (extReesGradedAlgebra_mul_comm I)).inv.right.hom.app (op U)
  let b := (deformationUngradedHom g I (I.comap g) le_rfl).right.hom.app (op U)
  let c := (ungradedToGradedRight Y B
    (extReesGradedAlgebra_mul_comm (I.comap g))).hom.app (op V)
  let z := extReesPullback g I (I.comap g) le_rfl n U x
  let w := (reesPieceComap g I (n.toNat : ℤ)).val.app (op U) x
  have hzw : z = w := extReesAmbient_injective (I.comap g) n V
    ((extReesAmbient_extReesPullback g I (I.comap g) le_rfl n U x).trans
      (extReesAmbient_reesPieceComap g I n U x).symm)
  change c.hom (b.hom (a.hom (A.ungradedIncl n x))) = B.ungradedIncl n w
  exact (congrArg (fun y => c.hom (b.hom y))
      (ungradedAlgebraSheafIsoGradedAlgebraSheaf_inv_ungradedIncl X A
        (extReesGradedAlgebra_mul_comm I) n U x)).trans
    ((congrArg c.hom (deformationUngradedHom_app_incl g I (I.comap g) le_rfl n U x)).trans
      ((ungradedToGradedRight_ungradedAlgebraSheafIncl Y B
        (extReesGradedAlgebra_mul_comm (I.comap g)) n V z).trans
          (congrArg (B.ungradedIncl n) hzw)))

private theorem extReesAlgebraPullbackHom_transpose :
    (algebraPullbackPushforwardAdjunction g).homEquiv
        (extReesAlgebraSheaf I) (extReesAlgebraSheaf (I.comap g))
        (extReesAlgebraPullbackHom g I) = deformationComapAlgebraHom g I := by
  let A := extReesGradedAlgebra I
  let B := extReesGradedAlgebra (I.comap g)
  let hA := extReesGradedAlgebra_mul_comm I
  let hB := extReesGradedAlgebra_mul_comm (I.comap g)
  let P := pbGraded g A
  let ψ := extReesGradedPullbackHom g I
  let hP := pbGraded_mul_comm g A hA
  let R := algebraPushforward g
  let a := algebraPullbackPushforwardAdjunction g
  let β := pushforwardHom g A hA
  let f := gradedAlgebraSheafMap Y ψ hP hB
  have h : (a.homEquiv _ _ (extReesAlgebraPullbackHom g I)) = β ≫ R.map f := by
    change a.homEquiv _ _ (comparison g A hA ≫ f) = _
    exact (a.homEquiv_naturality_right _ _).trans
      (congrArg (· ≫ R.map f)
        ((Adjunction.homEquiv_unit a _ _ _).trans (unit_comp_map_comparison g A hA)))
  refine h.trans (Under.UnderMorphism.ext (gradedAlgebraSheaf_right_hom_ext X A hA ?_))
  intro n W x
  obtain ⟨U⟩ := W
  let V := g ⁻¹ᵁ U
  let y := Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece n) (op U) x
  change (f.right.hom.app (op V)).hom
      ((β.right.hom.app (op U)).hom (A.ungradedIncl n x)) =
    ((deformationComapAlgebraHom g I).right.hom.app (op U)).hom (A.ungradedIncl n x)
  exact (congrArg (f.right.hom.app (op V)).hom (pushforwardHom_ungradedIncl g A hA U n x)).trans
    ((show (f.right.hom.app (op V)).hom (P.ungradedIncl n y) =
        B.ungradedIncl n ((ψ.app n).val.app (op V) y) from
          ungradedIncl_ungradedSheafMap ψ n y).trans
      ((congrArg (B.ungradedIncl n)
        (Stacks.RingedSpace.transposeApp_pullbackUnit g.toLRSHom.toShHom
          (extReesComapUnitalHom g I) n U x)).trans
            (deformationComapAlgebraHom_ungradedIncl g I n U x).symm))

private theorem relativeSpecMapOverBase_deformationComapAlgebraHom :
    relativeSpecMapOverBase g (extReesAlgebraSheaf I) (extReesAlgebraSheaf (I.comap g))
        (deformationComapAlgebraHom g I) = deformationMap g I (I.comap g) le_rfl := by
  let A := extReesAlgebraSheaf I
  let B := extReesAlgebraSheaf (I.comap g)
  let d := deformationMap g I (I.comap g) le_rfl
  let f : Over.mk (deformationSpaceToBase (I.comap g) ≫ g) ⟶
      Over.mk (deformationSpaceToBase I) :=
    Over.homMk d (deformationMap_toBase g I (I.comap g) le_rfl)
  apply Eq.symm
  refine relativeSpecMapOverBase_eq_of_pushforwardAlgebraMap g A B _ f ?_
  apply (cancel_epi (pushforwardAlgebraIso A).inv).mp
  have h : (pushforwardAlgebraIso A).inv ≫ pushforwardAlgebraMap f =
      deformationAlgebraHom g I (I.comap g) le_rfl := by
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    refine TopCat.Sheaf.hom_ext A.right.obj
      (pushforwardAlgebra (deformationSpaceToBase (I.comap g) ≫ g)).right
      (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens) fun U => ?_
    let p := deformationPair g I (I.comap g) le_rfl
    have hle := preimage_le_preimage_preimage f U.1
    have hle' : p.1 ⁻¹ᵁ U.1 ≤ pairToHom p ⁻¹ᵁ
        ((gluedSpectrum (extReesSituation I)).toBase ⁻¹ᵁ U.1) := hle
    let a := (universalAlgebraMap (extReesSituation I)).right.app (op U.1)
    let l := (pushforwardAlgebraMap f).right.hom.app (op U.1)
    let r := (deformationAlgebraHom g I (I.comap g) le_rfl).right.hom.app (op U.1)
    let m := d.appLE (deformationSpaceToBase I ⁻¹ᵁ U.1)
      ((deformationSpaceToBase (I.comap g) ≫ g) ⁻¹ᵁ U.1) hle
    have hl : l = m := pushforwardAlgebraMap_app f U.1 hle
    have hr : a ≫ m = r := pairToHom_appLE p U hle'
    change a ≫ l = r
    exact (congrArg (a ≫ ·) hl).trans hr
  refine h.trans ?_
  change deformationAlgebraHom g I (I.comap g) le_rfl = (pushforwardAlgebraIso A).inv ≫
    ((pushforwardAlgebraIso A).hom ≫ deformationComapAlgebraHom g I ≫
      (relativeSpecPushforwardIsoOverBase g B).inv)
  rw [Iso.inv_hom_id_assoc]
  let u := (ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)).inv
  let v := deformationUngradedHom g I (I.comap g) le_rfl
  let w := (algebraPushforward g).map (ungradedAlgebraSheafIsoGradedAlgebraSheaf Y
    (extReesGradedAlgebra (I.comap g)) (extReesGradedAlgebra_mul_comm (I.comap g))).hom
  let z := (relativeSpecPushforwardIsoOverBase g B).inv
  change u ≫ v ≫ w ≫ z = (u ≫ v ≫ w) ≫ z
  exact (congrArg (u ≫ ·) (Category.assoc v w z).symm).trans
    (Category.assoc u (v ≫ w) z).symm

/-- The first projection of the flat comparison is the native map of deformation spaces. -/
@[reassoc]
theorem deformationSpaceFlatPullbackIso_hom_fst [Flat g] :
    (deformationSpaceFlatPullbackIso g I).hom ≫ pullback.fst (deformationSpaceToBase I) g =
      deformationMap g I (I.comap g) le_rfl := by
  let A := extReesAlgebraSheaf I
  let B := extReesAlgebraSheaf (I.comap g)
  let e := extReesAlgebraPullbackIso g I
  let d := relativeSpecBaseChangeIso g A
  let f := relativeSpecMapOfAlgebraHom ((algebraPullback g).obj A) B e.hom
  let : IsAffineHom (Over.mk (relativeSpecToBase ((algebraPullback g).obj A))).hom :=
    isAffineHom_relativeSpecToBase _
  have h : (relativeSpecOverIso e).inv = f := by
    apply eq_of_pushforwardAlgebraMap_eq
    exact (pushforwardAlgebraMap_relativeSpecOverIso_inv e).trans
      (pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom _ _ _).symm
  change ((relativeSpecOverIso e).inv ≫ d.inv).left ≫ pullback.fst (relativeSpecToBase A) g = _
  rw [h]
  exact (relativeSpecBaseChangeMap_eq_relativeSpecMapOverBase g A B e.hom).trans
    ((congrArg (relativeSpecMapOverBase g A B) (extReesAlgebraPullbackHom_transpose g I)).trans
      (relativeSpecMapOverBase_deformationComapAlgebraHom g I))

end Stacks.Deformation

end
