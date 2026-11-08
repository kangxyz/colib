/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineComparison

/-! # Full-signature consumers for fixed-pair supported fine comparison -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

section ActualImage

variable [HasDerivedCategory.{d} U.Modules]

open SupportedOpenDerivedImage

example {E : CochainComplex U.Modules ℤ} (hE : complexObjects j T E) :
    ∃ (P : CochainComplex X.Modules ℤ) (M : CochainComplex U.Modules ℤ)
      (p : ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj P ⟶ M) (s : E ⟶ M),
      perfectSupported T.ι P ∧ perfectSupported (j ⁻¹ᵁ T).ι M ∧ QuasiIso p ∧ QuasiIso s :=
  exists_weak_cospan j T hE

example (hroof : HasDerivedRoofs j T) (P : CochainComplex X.Modules ℤ)
    (hP : perfectSupported T.ι P) (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j T B')
    (w : ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj P ⟶ B)
    [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : CochainComplex X.Modules ℤ) (D : CochainComplex U.Modules ℤ)
      (c : C ⟶ P) (d : D ⟶ B)
      (a : ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj C ⟶ D) (v : B' ⟶ D),
      perfectSupported T.ι C ∧ complexObjects j T D ∧ QuasiIso a ∧ QuasiIso v ∧
      a ≫ d = ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map c ≫ w ∧
      v ≫ d = b ∧ (∀ n, IsSplitEpi (c.f n)) ∧ (∀ n, IsSplitEpi (d.f n)) ∧
      perfectSupported T.ι (kernel c) ∧ complexObjects j T (kernel d) :=
  exists_dual_factorization j T hroof P hP B B' hB' w b

end ActualImage

/-- The always-valid image identity has no geometric hypotheses. -/
example : (perfectSupportedOpenKRestrict j T 0).range =
    (perfectSupportedKRestrict j T 0).range :=
  range_perfectSupportedOpenKRestrict_zero j T

section Geometry

variable [CompactSpace X] [QuasiSeparatedSpace X]
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

example (n : ℕ) : Function.Bijective (perfectSupportedOpenKRestrict j T (n + 1)) :=
  perfectSupportedOpenKRestrict_succ_bijective_of_union_compact j T hW n

example : Function.Injective (perfectSupportedOpenKRestrict j T 0) :=
  perfectSupportedOpenKRestrict_injective_of_union_compact j T hW 0

example : PerfectSupportedOpenCoarseK j T 0 ≃* (perfectSupportedKRestrict j T 0).range :=
  perfectSupportedOpenKZeroImageEquivOfUnionCompact j T hW

example (x : PerfectSupportedOpenCoarseK j T 0) :
    (perfectSupportedOpenKZeroImageEquivOfUnionCompact j T hW x :
      PerfectSupportedK (j ⁻¹ᵁ T).ι 0) = perfectSupportedOpenKRestrict j T 0 x := rfl

/-- Every exactness position includes the actual K-one to K-zero boundary. -/
example : (perfectSupportedKRestrict j T 1).range =
      (perfectSupportedConnectingHomOfUnionCompact j T hW 0).ker ∧
    (perfectSupportedConnectingHomOfUnionCompact j T hW 0).range =
      (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedKRestrict j T 0).ker :=
  perfectSupported_zeroTail_of_union_compact j T hW

example : (perfectSupportedConnectingHomOfUnionCompact j T hW 0).comp
    (perfectSupportedOpenKRestrict j T 1) = perfectSupportedOpenConnectingHom j T 0 :=
  perfectSupportedConnectingHomOfUnionCompact_comp_relative j T hW 0

example (δ : PerfectSupportedK (j ⁻¹ᵁ T).ι 1 →*
      PerfectSupportedK (T ⊔ j.opensRange).ι 0)
    (hδ : δ.comp (perfectSupportedOpenKRestrict j T 1) = perfectSupportedOpenConnectingHom j T 0) :
    δ = perfectSupportedConnectingHomOfUnionCompact j T hW 0 :=
  perfectSupportedConnectingHomOfUnionCompact_unique j T hW 0 δ hδ

end Geometry

example [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (hT : IsCompact (T : Set X)) (n : ℕ) :
    Function.Bijective (perfectSupportedOpenKRestrict j T (n + 1)) :=
  perfectSupportedOpenKRestrict_succ_bijective_of_qcqs j T hT n
