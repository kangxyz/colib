/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectShift
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectCofibrationSequence
public import Colib.Algebra.Homology.MappingCone.Identity
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import StacksFrontier.Homology.KFlat.Bifunctor

/-! # The sign of the shift on perfect-complex K-groups

The actual sequence `K ⟶ Cone(𝟙 K) ⟶ K[1]` gives additivity, and its
middle term is acyclic. Thus the shift acts by inversion in all
connective degrees, including zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CochainComplex

namespace AlgebraicGeometry.RingedSpace

universe u

variable (X : RingedSpace.{u, u})

local notation "P" => IsPerfectComplex (X := X)
local notation "Perf" => ObjectProperty.FullSubcategory P
local notation "A" => StrictlyPerfect.OXMod X
local notation "W" => perfectComplexesWaldhausen X

local instance : HasFiniteBiproducts (CochainComplex (StrictlyPerfect.OXMod.{u,u,u} X) ℤ) :=
  Abelian.hasFiniteBiproducts (C := CochainComplex (StrictlyPerfect.OXMod.{u,u,u} X) ℤ)

/-- The actual identity cone on the native perfect category. -/
def perfectIdentityCone : Perf ⥤ Perf :=
  ObjectProperty.lift P (ObjectProperty.ι P ⋙ identityConeFunctor)
    (fun K => isPerfectComplex_mappingCone (𝟙 K.obj) K.property K.property)

/-- The identity cone on the underlying complex is acyclic. -/
theorem perfectIdentityCone_acyclic (K : Perf) : ((perfectIdentityCone X).obj K).obj.Acyclic :=
  (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone (𝟙 K.obj)).1 inferInstance

/-- The actual cone sends all arrows to weak equivalences and preserves pushouts. -/
theorem perfectIdentityCone_exact :
    IsExact (W).cof (W).weq (W).cof (W).weq (perfectIdentityCone X) := by
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro K h
    apply IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι P)
    exact identityCone_isZero ((CofibrationClosedSubcategory.inclusion_exact
      (complexes A) P (perfectComplexes_cofibrationClosed X)).zero h)
  · intro K L f hf
    let : Mono f.hom := hf
    exact identityConeFunctor_map_mono f.hom
  · intro K L f _
    change QuasiIso ((perfectIdentityCone X).map f).hom
    refine (quasiIso_iff _).2 fun n => ?_
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso
      ((perfectIdentityCone_acyclic X K n).isZero_homology)
      ((perfectIdentityCone_acyclic X L n).isZero_homology) _
  · intro B C D E i f g j hi h
    apply IsPushout.of_map_of_faithful (ObjectProperty.ι P)
    exact identityConeFunctor_map_isPushout (CofibrationClosedSubcategory.inclusion_map_pushout
      (complexes A) P (perfectComplexes_cofibrationClosed X) hi h)

/-- The actual inclusion into the identity cone. -/
def perfectIdentityConeInclusion : 𝟭 Perf ⟶ perfectIdentityCone X where
  app K := ObjectProperty.homMk (mappingCone.inr (𝟙 K.obj))
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (𝟙 K.obj) (𝟙 L.obj) f.hom f.hom (by simp)).comm₂.symm

/-- The signed quotient of the identity cone is the native shift. -/
def perfectIdentityConeQuotient : perfectIdentityCone X ⟶ perfectShift X 1 where
  app K := ObjectProperty.homMk (mappingCone.triangle (𝟙 K.obj)).mor₃
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (𝟙 K.obj) (𝟙 L.obj) f.hom f.hom (by simp)).comm₃.symm

theorem perfectIdentityConeInclusion_quotient :
    perfectIdentityConeInclusion X ≫ perfectIdentityConeQuotient X = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (mappingCone.triangleRotateShortComplex (𝟙 K.obj)).zero

theorem perfectIdentityCone_cofibrationSequence :
    Additivity.IsCofibrationSequence W W
      (perfectIdentityConeInclusion X) (perfectIdentityConeQuotient X) :=
  perfectCofibrationSequence_of_shortExact W X _ _ (perfectIdentityConeInclusion_quotient X)
    (IsExact.id _ _) (perfectIdentityCone_exact X) (perfectShift_exact X 1)
    (fun K => coneSequence_shortExact K.obj)

theorem perfectIdentityCone_KMap_eq_one (n : ℕ) :
    KMap (perfectIdentityCone_exact X) n = 1 := by
  let z : perfectIdentityCone X ⟶ zeroFunctor (C := Perf) W := 0
  refine (KMap_eq_of_weakNatTrans (perfectIdentityCone_exact X)
    (zeroFunctor_isExact W W) z (fun K => ?_) n).trans (KMap_zeroFunctor W W n)
  change QuasiIso (z.app K).hom
  refine (quasiIso_iff _).2 fun q => ?_
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsZero.isIso ((perfectIdentityCone_acyclic X K q).isZero_homology)
    ((HomologicalComplex.acyclic_of_isZero _ ((ObjectProperty.ι P).map_isZero
      (W).isZero) q).isZero_homology) _

/-- The actual shift on the native K-group is multiplication by minus one. -/
theorem perfectShift_KMap_one_apply (n : ℕ) (x : (W).K n) :
    KMap (perfectShift_exact X 1) n x = x⁻¹ := by
  let : HasBinaryCoproducts Perf := Additivity.hasBinaryCoproducts W
  have h := Additivity.KMap_additivity_mul W W _ _ (perfectIdentityCone_cofibrationSequence X) n x
  change KMap (perfectIdentityCone_exact X) n x =
    KMap (IsExact.id (W).cof (W).weq) n x * KMap (perfectShift_exact X 1) n x at h
  simp only [perfectIdentityCone_KMap_eq_one, KMap_id, MonoidHom.one_apply,
    MonoidHom.id_apply] at h
  calc
    _ = (x⁻¹ * x) * KMap (perfectShift_exact X 1) n x := by rw [inv_mul_cancel, one_mul]
    _ = x⁻¹ := by rw [mul_assoc, ← h, mul_one]

end AlgebraicGeometry.RingedSpace
