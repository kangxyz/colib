/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.SupportedQcqsGeometry

/-!
# Full-signature supported qcqs geometry consumers

The targets remain global complexes and the numerator target only has quasi-coherent
homology. The local derived model is arbitrary. The complementary complex is the actual
shift and both support predicates use the literal inverse-image restriction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u d

variable {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) [HasDerivedCategory.{d} U.Modules]

omit [CompactSpace U] in
example (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))
    (A B : CochainComplex X.Modules ℤ) (hA : perfectSupported T.ι A)
    (hB : ∀ n : ℤ,
      ((HomologicalComplex.homologyFunctor X.Modules (.up ℤ) n).obj B).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ A) (a : R ⟶ B),
      perfectSupported T.ι R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map a) :=
  exists_perfectSupported_chainMap_roof_of_union_compact j T hW A B hA hB α

example (hT : IsCompact (T : Set X))
    (A B : CochainComplex X.Modules ℤ) (hA : perfectSupported T.ι A)
    (hB : ∀ n : ℤ,
      ((HomologicalComplex.homologyFunctor X.Modules (.up ℤ) n).obj B).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ A) (a : R ⟶ B),
      perfectSupported T.ι R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map a) :=
  exists_perfectSupported_chainMap_roof_of_qcqs j T hT A B hA hB α

omit [CompactSpace U] in
example (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      perfectSupported T.ι R ∧ perfectSupported (j ⁻¹ᵁ T).ι C ∧ C = E⟦(1 : ℤ)⟧ ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (E ⊞ C)) := by
  obtain ⟨R, hR, hC, he⟩ :=
    exists_perfectSupported_restrict_stabilization_of_union_compact j T hW E hE
  exact ⟨R, E⟦(1 : ℤ)⟧, hR, hC, rfl, he⟩

example (hT : IsCompact (T : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ R : CochainComplex X.Modules ℤ, perfectSupported T.ι R ∧
      perfectSupported (j ⁻¹ᵁ T).ι (E⟦(1 : ℤ)⟧) ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (E ⊞ E⟦(1 : ℤ)⟧)) :=
  exists_perfectSupported_restrict_stabilization_of_qcqs j T hT E hE

example {N : CochainComplex U.Modules ℤ} {A : CochainComplex X.Modules ℤ}
    (s : N ⟶ ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) :
    (Complex.extensionByZeroAdjunction j).unit.app N ≫
        ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
          ((Complex.extensionByZero j).map s ≫
            (Complex.extensionByZeroAdjunction j).counit.app A) = s :=
  extensionByZero_unit_restrict_counit_lift j s

end
