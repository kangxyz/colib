/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageOriginalTarget
/-! # The original target projection remains étale over a coefficient extension

The coefficient field F can differ from the transfer ground field K. Finiteness
and separability of E/K imply the corresponding facts for E/F. The literal
second tensor projection and its retained open chart are therefore étale.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The second tensor projection is the base change of the finite étale field map. -/
theorem finiteStageOriginalTarget_etale
    (F E B : Type u) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    [CommRing B] [Algebra F B] : Etale (finiteStageOriginalTarget F E B) := by
  let : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  let : Algebra.FinitePresentation F E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale F E := {}
  let : Algebra.Etale B (E ⊗[F] B) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight F B E)
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact (RingHom.etale_algebraMap (R := B) (S := E ⊗[F] B)).mpr inferInstance

/-- Finiteness and separability over K suffice for the coefficient-field projection. -/
theorem finiteStageOriginalTarget_tower_etale
    (K F E B : Type u) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    [CommRing B] [Algebra F B] : Etale (finiteStageOriginalTarget F E B) := by
  let : Module.Finite F E := Module.Finite.of_restrictScalars_finite K F E
  let : Algebra.IsSeparable F E := Algebra.isSeparable_tower_top_of_isSeparable K F E
  exact finiteStageOriginalTarget_etale F E B

/-- The literal intersection of the two retained opens maps étale to the original target. -/
theorem finiteStageRetainedOriginalTarget_tower_etale
    (K F E B : Type u) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    [CommRing B] [Algebra F B] (re r : E ⊗[F] B) :
    let je := Spec.map (CommRingCat.ofHom
      (algebraMap (E ⊗[F] B) (Localization.Away re)))
    let jr := Scheme.Opens.ι (X := Spec (.of (E ⊗[F] B))) (PrimeSpectrum.basicOpen r)
    Etale ((pullback.snd je jr ≫ jr) ≫ finiteStageOriginalTarget F E B) := by
  intro je jr
  let : IsOpenImmersion je := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap (E ⊗[F] B) (Localization.Away re)))))
  let : IsOpenImmersion jr :=
    @Scheme.Opens.instIsOpenImmersionι (Spec (.of (E ⊗[F] B))) (PrimeSpectrum.basicOpen r)
  let : Etale (finiteStageOriginalTarget F E B) :=
    finiteStageOriginalTarget_tower_etale K F E B
  infer_instance

end AlgebraicGeometry.Scheme
