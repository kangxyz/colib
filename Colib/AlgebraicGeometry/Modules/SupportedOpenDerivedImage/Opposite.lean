/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Exact
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedOpposite
public import Colib.CategoryTheory.Waldhausen.ComplexFunctor

/-! # Actual opposite structure on the honest restriction image

The original image category carries admissible epimorphisms on its literal opposite.
Actual kernel and cokernel membership identify these maps with ambient epis and monos.
The existing ambient-monomorphism Waldhausen structure stays unchanged. The only
geometric input is the explicitly displayed global-perfect-model roof property.

Implementation provenance: `OpenDerivedImage/Structure.lean:42-109` in Quillen's
`AlgebraicGeometry/PerfectComplexes` at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j T)]

/-- Admissibility is exactly monicity of the original chain map. -/
theorem inflation_iff {K L : Obj j T} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j T)).inflation f ↔ Mono f.hom := by
  constructor
  · rintro ⟨Q, p, w, hS⟩
    exact hS.mono_f
  · intro hf
    let : Mono f.hom := hf
    let S := ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f.hom }
    exact ⟨⟨cokernel f.hom,
      complexObjects_quotient_of_shortExact j T Fact.out hS K.property L.property⟩,
      ObjectProperty.homMk (cokernel.π f.hom),
      ObjectProperty.hom_ext _ (cokernel.condition f.hom), hS⟩

/-- Every ambient epimorphism has its actual kernel in the honest image. -/
theorem deflation_iff {K L : Obj j T} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j T)).deflation f ↔ Epi f.hom := by
  constructor
  · rintro ⟨Q, p, w, hS⟩
    exact hS.epi_g
  · intro hf
    let : Epi f.hom := hf
    let S := ShortComplex.mk (kernel.ι f.hom) f.hom (kernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact f.hom }
    exact ⟨⟨kernel f.hom,
      complexObjects_kernel_of_shortExact j T Fact.out hS K.property L.property⟩,
      ObjectProperty.homMk (kernel.ι f.hom),
      ObjectProperty.hom_ext _ (kernel.condition f.hom), hS⟩

/-- Admissible epimorphisms on the literal opposite of the original image category. -/
def oppositeWaldhausen : Structure (Obj j T)ᵒᵖ := oppositeComplexSubcategory (complexObjects j T)

/-- Compatibility with the unchanged ambient-monomorphism image structure. -/
theorem oppositeWaldhausen_compatible :
    IsCompatibleDual (waldhausen j T Fact.out) (oppositeWaldhausen j T) := by
  apply exactDualStructure_compatible
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j T))
    (waldhausen j T Fact.out) (complexSubcategoryPullbackGluing (complexObjects j T))
  funext K L f
  exact propext (inflation_iff j T f).symm

/-- The actual common opposite cylinder supplies image joint data. -/
def oppositeJointData : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (oppositeWaldhausen j T)) :=
  oppositeComplexJointData (complexObjects j T) (fun _ h => complexObjects_shift j T h (-1))

/-- The unchanged corestriction is exact on the actual opposite structures. -/
theorem corestrict_op_isExact : IsExact
    (perfectSupportedOppositeWaldhausen T.ι).cof
    (perfectSupportedOppositeWaldhausen T.ι).weq
    (oppositeWaldhausen j T).cof (oppositeWaldhausen j T).weq (corestrict j T).op :=
  complexSubcategoryMap_op_exact
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
