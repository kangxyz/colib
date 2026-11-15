/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OneSection
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.GlobalParameter
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.QuasiRegularNormalCone
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured

/-!
# The normal fibre for a smooth pair

For an immersion between schemes smooth over the same base, the canonical map
from the normal cone to the normal bundle is invertible. Transporting the
existing closed embedding of the cone into the extended-Rees deformation
space along this isomorphism gives the normal-bundle fibre map. Its ideal is
the zero scheme of the original deformation parameter.

These are statements about the actual Stacks relative spectra and their
canonical maps. Smoothness of the deformation space and motivic purity are
separate obligations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Conormal

universe u

namespace Stacks.Conormal

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ S)
  [IsImmersion i] [Smooth p] [Smooth (i ≫ p)]

include p in
/-- The canonical normal-cone comparison is invertible for a smooth pair. -/
theorem isIso_normalConeToNormalBundle_of_smooth :
    IsIso (normalConeToNormalBundle i) :=
  isIso_normalConeToNormalBundle_of_isRegularImmersion i
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i p)

/-- The canonical normal-cone identification for an immersion of smooth schemes. -/
def normalConeIsoNormalBundleOfSmooth : normalCone i ≅ normalBundle i :=
  @asIso _ _ _ _ (normalConeToNormalBundle i)
    (isIso_normalConeToNormalBundle_of_smooth i p)

@[simp]
theorem normalConeIsoNormalBundleOfSmooth_hom :
    (normalConeIsoNormalBundleOfSmooth i p).hom = normalConeToNormalBundle i := rfl

@[reassoc]
theorem normalConeIsoNormalBundleOfSmooth_hom_toBase :
    (normalConeIsoNormalBundleOfSmooth i p).hom ≫ normalBundleToBase i =
      normalConeToBase i :=
  normalConeToNormalBundle_normalBundleToBase i

@[reassoc (attr := simp)]
theorem normalConeIsoNormalBundleOfSmooth_inv_toBase :
    (normalConeIsoNormalBundleOfSmooth i p).inv ≫ normalConeToBase i =
      normalBundleToBase i := by
  rw [← normalConeIsoNormalBundleOfSmooth_hom_toBase i p,
    Iso.inv_hom_id_assoc]

end Stacks.Conormal

namespace Stacks.Deformation

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ S)
  [IsImmersion i] [Smooth p] [Smooth (i ≫ p)]

/-- The normal-bundle fibre map into the extended-Rees deformation of a smooth pair. -/
def normalBundleToDeformation :
    normalBundle i ⟶ deformationSpace (coborderIdeal i) :=
  (normalConeIsoNormalBundleOfSmooth i p).inv ≫ normalConeToDeformation i

/-- The normal-bundle fibre map is the original normal-cone embedding under the
canonical normal-cone identification. -/
@[reassoc]
theorem normalConeIsoNormalBundleOfSmooth_hom_toDeformation :
    (normalConeIsoNormalBundleOfSmooth i p).hom ≫ normalBundleToDeformation i p =
      normalConeToDeformation i := by
  rw [normalBundleToDeformation, Iso.hom_inv_id_assoc]

/-- The normal-bundle fibre map is a closed immersion. -/
instance isClosedImmersion_normalBundleToDeformation :
    IsClosedImmersion (normalBundleToDeformation i p) := by
  dsimp [normalBundleToDeformation]
  infer_instance

/-- The normal-bundle fibre map lies over the original immersion into its coborder. -/
@[reassoc]
theorem normalBundleToDeformation_toBase :
    normalBundleToDeformation i p ≫ deformationSpaceToBase (coborderIdeal i) =
      normalBundleToBase i ≫ i.liftCoborder := by
  rw [normalBundleToDeformation, Category.assoc, normalConeToDeformation_toBase,
    normalConeIsoNormalBundleOfSmooth_inv_toBase_assoc]

/-- The normal-bundle fibre map lies over the original immersion into the ambient scheme. -/
@[reassoc]
theorem normalBundleToDeformation_toAmbient :
    normalBundleToDeformation i p ≫
        (deformationSpaceToBase (coborderIdeal i) ≫ i.coborderRange.ι) =
      normalBundleToBase i ≫ i := by
  rw [← Category.assoc, normalBundleToDeformation_toBase, Category.assoc,
    Scheme.Hom.liftCoborder_ι]

/-- The scheme-theoretic normal fibre is cut out by the original parameter. -/
theorem ker_normalBundleToDeformation :
    (normalBundleToDeformation i p).ker =
      Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
        (Scheme.unitModule (deformationSpace (coborderIdeal i)))
        (paramGlobal (coborderIdeal i)) := by
  rw [normalBundleToDeformation, Scheme.Hom.ker_comp_of_isIso,
    ker_normalConeToDeformation]

/-- The parameter-zero subscheme of the deformation is the actual normal bundle
for a smooth pair. -/
def parameterZeroIsoNormalBundle :
    (Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
      (Scheme.unitModule (deformationSpace (coborderIdeal i)))
      (paramGlobal (coborderIdeal i))).subscheme ≅ normalBundle i := by
  let F := Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
    (Scheme.unitModule (deformationSpace (coborderIdeal i))) (paramGlobal (coborderIdeal i))
  have hker : (normalBundleToDeformation i p).ker = F.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_normalBundleToDeformation]
  have := IsClosedImmersion.isIso_lift (normalBundleToDeformation i p) F.subschemeι hker
  exact asIso (IsClosedImmersion.lift (normalBundleToDeformation i p) F.subschemeι hker.le)

/-- The canonical normal-fibre identification retains the actual closed fibre map. -/
@[reassoc (attr := simp)]
theorem parameterZeroIsoNormalBundle_hom_comp :
    (parameterZeroIsoNormalBundle i p).hom ≫ normalBundleToDeformation i p =
      (Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
        (Scheme.unitModule (deformationSpace (coborderIdeal i)))
        (paramGlobal (coborderIdeal i))).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- Positive homogeneous sections of the extended-Rees algebra of the zero ideal
vanish over every open, with no affineness assumption. -/
theorem extReesAmbient_bot_eq_zero_of_pos (T : Scheme.{u}) (n : ℤ) (hn : 0 < n)
    (U : T.Opens)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (Opposite.op U)) :
    extReesAmbient (⊥ : T.IdealSheafData) n U x = 0 := by
  have hn' : n.toNat ≠ 0 := by omega
  have hpow : (⊥ : T.IdealSheafData) ^ n.toNat = ⊥ := by
    ext V
    simp [hn']
  have : IsIso (((⊥ : T.IdealSheafData) ^ n.toNat).subschemeι) := by
    rw [hpow]
    infer_instance
  have hinj := (ConcreteCategory.bijective_of_isIso
    (((⊥ : T.IdealSheafData) ^ n.toNat).subschemeι.app U)).1
  have hx := congrArg (fun f => f.val.app (Opposite.op U) x)
    (CategoryTheory.Limits.kernel.condition (SheafOfModules.unitToPushforwardObjUnit
      ((⊥ : T.IdealSheafData) ^ n.toNat).subschemeι.toRingCatSheafHom))
  change (((⊥ : T.IdealSheafData) ^ n.toNat).subschemeι.app U).hom
    (extReesAmbient (⊥ : T.IdealSheafData) n U x) = 0 at hx
  exact hinj (hx.trans (map_zero _).symm)

/-- The additive degree-zero projection of the original extended-Rees algebra of zero. -/
def extReesBotEvalZeroAdd (T : Scheme.{u}) (U : T.Opens) :
    (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.Total (Opposite.op U) →+
      Γ(T, U) :=
  (AddMonoidHom.mk' (extReesAmbient (⊥ : T.IdealSheafData) 0 U)
    (extReesAmbient_add (⊥ : T.IdealSheafData) 0 U)).comp
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.degreeZeroComponent
        (Opposite.op U))

/-- Degree zero is retained by evaluation at zero. -/
@[simp]
theorem extReesBotEvalZeroAdd_incl_zero (T : Scheme.{u}) (U : T.Opens)
    (x : (extReesPiece (⊥ : T.IdealSheafData) 0).val.obj (Opposite.op U)) :
    extReesBotEvalZeroAdd T U
        ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl 0 x) =
      extReesAmbient (⊥ : T.IdealSheafData) 0 U x := by
  change extReesAmbient (⊥ : T.IdealSheafData) 0 U
    ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.degreeZeroComponent
      (Opposite.op U)
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl 0 x)) = _
  exact congrArg (extReesAmbient (⊥ : T.IdealSheafData) 0 U)
    (Stacks.GradedAlgebra.degreeZeroComponent_incl_self
      (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra (Opposite.op U) x)

/-- Every nonzero degree is killed by evaluation at zero. -/
theorem extReesBotEvalZeroAdd_incl_of_ne (T : Scheme.{u}) (U : T.Opens) (n : ℤ) (hn : n ≠ 0)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (Opposite.op U)) :
    extReesBotEvalZeroAdd T U
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x) = 0 := by
  change extReesAmbient (⊥ : T.IdealSheafData) 0 U
    ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.degreeZeroComponent
      (Opposite.op U)
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x)) = 0
  exact (congrArg (extReesAmbient (⊥ : T.IdealSheafData) 0 U)
    (Stacks.GradedAlgebra.degreeZeroComponent_incl_of_ne
      (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra
        hn (Opposite.op U) x)).trans
        (extReesAmbient_zero (⊥ : T.IdealSheafData) 0 U)

-- The multiplicativity argument is the nonpositive-degree form of
-- `Stacks.GradedAlgebra.augmentation_mul_incl` in DeRham/LineBundle/Punctured.
private theorem extReesBotEvalZeroAdd_mul_incl (T : Scheme.{u}) (U : T.Opens) (n m : ℤ)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (Opposite.op U))
    (y : (extReesPiece (⊥ : T.IdealSheafData) m).val.obj (Opposite.op U)) :
    let A := (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra
    extReesBotEvalZeroAdd T U (A.incl n x * A.incl m y) =
      extReesBotEvalZeroAdd T U (A.incl n x) * extReesBotEvalZeroAdd T U (A.incl m y) := by
  dsimp only
  let A := (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra
  let f := extReesBotEvalZeroAdd T U
  by_cases hnm : n + m = 0
  · by_cases hn : n = 0
    · have hm : m = 0 := by omega
      subst n m
      refine (congrArg f (A.incl_mul_incl 0 0 x y)).trans ?_
      exact (extReesBotEvalZeroAdd_incl_zero T U _).trans
        ((extReesAmbient_extReesMul (⊥ : T.IdealSheafData) 0 0 U x y).trans
          (congrArg₂ (· * ·) (extReesBotEvalZeroAdd_incl_zero T U x).symm
            (extReesBotEvalZeroAdd_incl_zero T U y).symm))
    · rcases (by omega : 0 < n ∨ 0 < m) with hnpos | hmpos
      · have hx : x = 0 := extReesAmbient_injective (⊥ : T.IdealSheafData) n U
          ((extReesAmbient_bot_eq_zero_of_pos T n hnpos U x).trans
            (extReesAmbient_zero (⊥ : T.IdealSheafData) n U).symm)
        have hx' : A.incl n x = 0 := (congrArg (A.incl n) hx).trans (A.incl_zero n)
        have hl : f (A.incl n x * A.incl m y) = 0 :=
          (congrArg f ((congrArg (fun a => a * A.incl m y) hx').trans (zero_mul _))).trans
            f.map_zero
        exact hl.trans ((congrArg (fun a => a * f (A.incl m y))
          ((congrArg f hx').trans f.map_zero)).trans (zero_mul _)).symm
      · have hy : y = 0 := extReesAmbient_injective (⊥ : T.IdealSheafData) m U
          ((extReesAmbient_bot_eq_zero_of_pos T m hmpos U y).trans
            (extReesAmbient_zero (⊥ : T.IdealSheafData) m U).symm)
        have hy' : A.incl m y = 0 := (congrArg (A.incl m) hy).trans (A.incl_zero m)
        have hl : f (A.incl n x * A.incl m y) = 0 :=
          (congrArg f ((congrArg (fun a => A.incl n x * a) hy').trans (mul_zero _))).trans
            f.map_zero
        exact hl.trans ((congrArg (fun a => f (A.incl n x) * a)
          ((congrArg f hy').trans f.map_zero)).trans (mul_zero _)).symm
  · have hl : f (A.incl n x * A.incl m y) = 0 :=
      (congrArg f (A.incl_mul_incl n m x y)).trans
        (extReesBotEvalZeroAdd_incl_of_ne T U (n + m) hnm _)
    by_cases hn : n = 0
    · have hm : m ≠ 0 := by omega
      exact hl.trans ((congrArg (fun a => f (A.incl n x) * a)
        (extReesBotEvalZeroAdd_incl_of_ne T U m hm y)).trans (mul_zero _)).symm
    · exact hl.trans ((congrArg (fun a => a * f (A.incl m y))
        (extReesBotEvalZeroAdd_incl_of_ne T U n hn x)).trans (zero_mul _)).symm

/-- Evaluation at zero on the original extended-Rees algebra of the zero ideal. -/
def extReesBotEvalZero (T : Scheme.{u}) (U : T.Opens) :
    (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.Total (Opposite.op U) →+*
      Γ(T, U) :=
  { extReesBotEvalZeroAdd T U with
    map_one' := by
      change extReesBotEvalZeroAdd T U 1 = 1
      exact (extReesBotEvalZeroAdd_incl_zero T U
        ((extReesOne (⊥ : T.IdealSheafData)).eval (Opposite.op U))).trans
          (extReesAmbient_extReesOne (⊥ : T.IdealSheafData) (Opposite.op U))
    map_mul' := by
      intro a b
      change extReesBotEvalZeroAdd T U (a * b) =
        extReesBotEvalZeroAdd T U a * extReesBotEvalZeroAdd T U b
      induction a using Stacks.GradedAlgebra.incl_induction with
      | zero => simp only [zero_mul, map_zero]
      | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
      | incl n x =>
          induction b using Stacks.GradedAlgebra.incl_induction with
          | zero => simp only [mul_zero, map_zero]
          | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
          | incl m y => exact extReesBotEvalZeroAdd_mul_incl T U n m x y }

/-- Evaluation at zero retains degree zero. -/
@[simp]
theorem extReesBotEvalZero_incl_zero (T : Scheme.{u}) (U : T.Opens)
    (x : (extReesPiece (⊥ : T.IdealSheafData) 0).val.obj (Opposite.op U)) :
    extReesBotEvalZero T U
        ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl 0 x) =
      extReesAmbient (⊥ : T.IdealSheafData) 0 U x :=
  extReesBotEvalZeroAdd_incl_zero T U x

/-- Evaluation at zero kills every homogeneous section of nonzero degree. -/
theorem extReesBotEvalZero_incl_of_ne (T : Scheme.{u}) (U : T.Opens) (n : ℤ) (hn : n ≠ 0)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (Opposite.op U)) :
    extReesBotEvalZero T U
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x) = 0 :=
  extReesBotEvalZeroAdd_incl_of_ne T U n hn x

/-- Evaluation at zero commutes with restriction of sections. -/
theorem extReesBotEvalZero_restrict (T : Scheme.{u}) {U V : T.Opens} (h : V ≤ U)
    (x : (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.Total
      (Opposite.op U)) :
    extReesBotEvalZero T V
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.totalRestrict
        (homOfLE h).op x) = T.presheaf.map (homOfLE h).op (extReesBotEvalZero T U x) := by
  let A := (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra
  change extReesAmbient (⊥ : T.IdealSheafData) 0 V
      (A.degreeZeroComponent (Opposite.op V) (A.totalRestrict (homOfLE h).op x)) =
    T.presheaf.map (homOfLE h).op
      (extReesAmbient (⊥ : T.IdealSheafData) 0 U (A.degreeZeroComponent (Opposite.op U) x))
  exact (congrArg (extReesAmbient (⊥ : T.IdealSheafData) 0 V)
    (A.degreeZeroComponent_totalRestrict (homOfLE h).op x)).trans
      (extReesAmbient_restrict (⊥ : T.IdealSheafData) 0 V U h _)

open Opposite Stacks.RelativeSpec in
/-- The canonical evaluation at zero on the presheaf extended-Rees algebra of zero. -/
def extReesBotEvalZeroPresheaf (T : Scheme.{u}) :
    ungradedCommPresheaf T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
      (extReesGradedAlgebra_mul_comm _) ⟶ T.presheaf where
  app W := @CommRingCat.ofHom _ _
    ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.commRingTotal
      (extReesGradedAlgebra_mul_comm _) W) _ (extReesBotEvalZero T W.unop)
  naturality W W' f := by
    have h : W'.unop ≤ W.unop := leOfHom f.unop
    obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
    exact CommRingCat.hom_ext (RingHom.ext (extReesBotEvalZero_restrict T h))

open Opposite Stacks.RelativeSpec in
/-- Evaluation at zero fixes the original structure sheaf. -/
theorem structureMap_comp_extReesBotEvalZeroPresheaf (T : Scheme.{u}) :
    ungradedCommStructureMap T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
        (extReesGradedAlgebra_mul_comm _) ≫ extReesBotEvalZeroPresheaf T = 𝟙 T.presheaf := by
  refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  let r' : T.ringCatSheaf.obj.obj W := r
  change extReesBotEvalZero T W.unop
    (r' • (1 : (extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.Total W)) = r
  rw [Stacks.GradedAlgebra.one_eq_incl, ← Stacks.GradedAlgebra.incl_smul]
  let x := (extReesOne (⊥ : T.IdealSheafData)).eval W
  refine (extReesBotEvalZero_incl_zero T W.unop (r' • x)).trans ?_
  exact (extReesAmbient_smul (⊥ : T.IdealSheafData) 0 W.unop r' x).trans
    ((congrArg (Stacks.Blowup.ringSectionToGamma r' * ·)
      (extReesAmbient_extReesOne (⊥ : T.IdealSheafData) W)).trans (mul_one _))

open Stacks.RelativeSpec in
/-- Evaluation at zero on the sheafification of the original zero-ideal Rees algebra. -/
def extReesBotEvalZeroUngraded (T : Scheme.{u}) :
    ungradedAlgebraSheaf T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
      (extReesGradedAlgebra_mul_comm _) ⟶ Under.mk (𝟙 T.sheaf) :=
  (ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra (⊥ : T.IdealSheafData))
    (extReesGradedAlgebra_mul_comm _) (Under.mk (𝟙 T.sheaf))).symm
      ⟨extReesBotEvalZeroPresheaf T, structureMap_comp_extReesBotEvalZeroPresheaf T⟩

open Stacks.RelativeSpec in
/-- Evaluation at zero on the actual algebra sheaf defining the zero-ideal deformation. -/
def extReesBotEvalZeroAlgebraHom (T : Scheme.{u}) :
    extReesAlgebraSheaf (⊥ : T.IdealSheafData) ⟶ Under.mk (𝟙 T.sheaf) :=
  (ungradedAlgebraSheafIsoGradedAlgebraSheaf T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
    (extReesGradedAlgebra_mul_comm _)).inv ≫ extReesBotEvalZeroUngraded T

/-- The original structure algebra map is a section of evaluation at zero. -/
theorem hom_comp_extReesBotEvalZeroAlgebraHom (T : Scheme.{u}) :
    (extReesAlgebraSheaf (⊥ : T.IdealSheafData)).hom.hom ≫
      (extReesBotEvalZeroAlgebraHom T).right.hom = 𝟙 T.presheaf :=
  congrArg (fun f : T.sheaf ⟶ T.sheaf => f.hom) (Under.w (extReesBotEvalZeroAlgebraHom T))

open Opposite Stacks.RelativeSpec in
/-- Sheafified evaluation at zero agrees with the original evaluation on homogeneous sections. -/
theorem extReesBotEvalZeroUngraded_incl (T : Scheme.{u}) (U : T.Opens) (n : ℤ)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (op U)) :
    ((extReesBotEvalZeroUngraded T).right.hom.app (op U)).hom
      (ungradedAlgebraSheafIncl T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
        (extReesGradedAlgebra_mul_comm _) n U x) =
    extReesBotEvalZero T U
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x) := by
  have h : ungradedCommToSheaf T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
      (extReesGradedAlgebra_mul_comm _) ≫ (extReesBotEvalZeroUngraded T).right.hom =
      extReesBotEvalZeroPresheaf T :=
    congrArg Subtype.val
      ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra (⊥ : T.IdealSheafData))
        (extReesGradedAlgebra_mul_comm _) (Under.mk (𝟙 T.sheaf))).apply_symm_apply
          ⟨extReesBotEvalZeroPresheaf T, structureMap_comp_extReesBotEvalZeroPresheaf T⟩)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op U))
    ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x)

open Opposite Stacks.RelativeSpec in
/-- Evaluation at zero retains the original algebra-sheaf realization of each
homogeneous section. -/
theorem extReesBotEvalZeroAlgebraHom_app_incl (T : Scheme.{u}) (U : T.Opens) (n : ℤ)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (op U)) :
    ((extReesBotEvalZeroAlgebraHom T).right.hom.app (op U)).hom
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf T
        (extReesGradedAlgebra (⊥ : T.IdealSheafData))
        (extReesGradedAlgebra_mul_comm _)).hom.right.hom.app (op U)).hom
          (ungradedAlgebraSheafIncl T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
            (extReesGradedAlgebra_mul_comm _) n U x)) =
    extReesBotEvalZero T U
      ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x) := by
  let e := ungradedAlgebraSheafIsoGradedAlgebraSheaf T
    (extReesGradedAlgebra (⊥ : T.IdealSheafData)) (extReesGradedAlgebra_mul_comm _)
  have he (a) : (e.inv.right.hom.app (op U)).hom ((e.hom.right.hom.app (op U)).hom a) = a :=
    congrArg (fun f => (f.right.hom.app (op U)).hom a) e.hom_inv_id
  change ((extReesBotEvalZeroUngraded T).right.hom.app (op U)).hom
    ((e.inv.right.hom.app (op U)).hom ((e.hom.right.hom.app (op U)).hom
      (ungradedAlgebraSheafIncl T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
        (extReesGradedAlgebra_mul_comm _) n U x))) = _
  rw [he]
  exact extReesBotEvalZeroUngraded_incl T U n x

/-- The canonical parameter-zero section of the original zero-ideal deformation. -/
def deformationZeroSectionBot (T : Scheme.{u}) : T ⟶ deformationSpace (⊥ : T.IdealSheafData) :=
  Stacks.RelativeSpec.retractionSection (extReesSituation (⊥ : T.IdealSheafData))
    (extReesBotEvalZeroAlgebraHom T).right.hom (hom_comp_extReesBotEvalZeroAlgebraHom T)

/-- The canonical zero section splits the original deformation projection. -/
@[reassoc (attr := simp)]
theorem deformationZeroSectionBot_toBase (T : Scheme.{u}) :
    deformationZeroSectionBot T ≫ deformationSpaceToBase (⊥ : T.IdealSheafData) = 𝟙 T :=
  Stacks.RelativeSpec.retractionSection_comp_toBase (extReesSituation (⊥ : T.IdealSheafData))
    (extReesBotEvalZeroAlgebraHom T).right.hom (hom_comp_extReesBotEvalZeroAlgebraHom T)

/-- The canonical parameter-zero section is a closed immersion. -/
instance isClosedImmersion_deformationZeroSectionBot (T : Scheme.{u}) :
    IsClosedImmersion (deformationZeroSectionBot T) :=
  Stacks.RelativeSpec.isClosedImmersion_retractionSection
    (extReesSituation (⊥ : T.IdealSheafData)) (extReesBotEvalZeroAlgebraHom T).right.hom
    (hom_comp_extReesBotEvalZeroAlgebraHom T)

open Opposite Stacks.RelativeSpec in
/-- The actual zero section evaluates homogeneous functions by the canonical degree-zero map. -/
theorem deformationZeroSectionBot_appLE_chartIncl (T : Scheme.{u}) (W : T.affineOpens) (n : ℤ)
    (x : (extReesPiece (⊥ : T.IdealSheafData) n).val.obj (op W.1))
    (h : W.1 ≤ deformationZeroSectionBot T ⁻¹ᵁ
      (deformationSpaceToBase (⊥ : T.IdealSheafData) ⁻¹ᵁ W.1)) :
    ((deformationZeroSectionBot T).appLE
      (deformationSpaceToBase (⊥ : T.IdealSheafData) ⁻¹ᵁ W.1) W.1 h).hom
        (chartIncl (⊥ : T.IdealSheafData) n W.1 x) =
      extReesBotEvalZero T W.1
        ((extReesGradedAlgebra (⊥ : T.IdealSheafData)).toPresheafGradedAlgebra.incl n x) := by
  have hp := pairToHom_appLE
    (retractionPair (extReesSituation (⊥ : T.IdealSheafData))
      (extReesBotEvalZeroAlgebraHom T).right.hom (hom_comp_extReesBotEvalZeroAlgebraHom T)) W h
  exact (ConcreteCategory.congr_hom hp
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf T
      (extReesGradedAlgebra (⊥ : T.IdealSheafData))
      (extReesGradedAlgebra_mul_comm _)).hom.right.hom.app (op W.1)).hom
        (ungradedAlgebraSheafIncl T (extReesGradedAlgebra (⊥ : T.IdealSheafData))
          (extReesGradedAlgebra_mul_comm _) n W.1 x))).trans
            (extReesBotEvalZeroAlgebraHom_app_incl T W.1 n x)

/-- The actual zero section pulls the original deformation parameter back to zero. -/
theorem deformationZeroSectionBot_appLE_paramChartOf (T : Scheme.{u}) (W : T.affineOpens)
    (h : W.1 ≤ deformationZeroSectionBot T ⁻¹ᵁ
      (deformationSpaceToBase (⊥ : T.IdealSheafData) ⁻¹ᵁ W.1)) :
    ((deformationZeroSectionBot T).appLE
      (deformationSpaceToBase (⊥ : T.IdealSheafData) ⁻¹ᵁ W.1) W.1 h).hom
      (paramChartOf (⊥ : T.IdealSheafData) W.1) = 0 :=
  (deformationZeroSectionBot_appLE_chartIncl T W (-1) (paramPiece _ W.1) h).trans
    (extReesBotEvalZero_incl_of_ne T W.1 (-1) (by omega) (paramPiece _ W.1))

end Stacks.Deformation

end
