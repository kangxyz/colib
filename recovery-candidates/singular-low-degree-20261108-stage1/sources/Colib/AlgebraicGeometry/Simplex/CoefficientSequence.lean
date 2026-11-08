/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.NisnevichSheafification
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Coefficient exact sequences for the actual ordinary singular chains

A short exact sequence of ordinary presheaves induces the native connecting
map on the homology of the existing singular-chain complexes. The original
coefficient maps, the native connecting morphism and its sign convention form
a six-object exact sequence. In degree zero the last map is an epimorphism,
giving the usual right-exact tail. Naturality is proved for actual morphisms
of coefficient short exact sequences and, since these are presheaf maps, for
restriction along arbitrary smooth-site morphisms.

The same exact sequence is obtained after actual degreewise Nisnevich
sheafification. This statement does not identify its connecting morphism
with sheafification of the presheaf connecting morphism; such compatibility
requires a separate comparison. No transfer category or replacement cone is
assumed. The coefficient category is abelian; the sheaf-valued assertions
add exactly the native `HasSheafify` hypothesis.

The native input is Mathlib's homology sequence (Stacks Tag 0111), applied to
the exact functors proved in `Exactness` and `NisnevichSheafification`.
MVW2006, Definition 2.14, printed p. 16, is background for the ordinary
singular construction, not a literal source for these generalized endpoints.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (hS : S.ShortExact)

/-- The native connecting morphism of the actual singular-chain coefficient sequence. -/
def singularCoefficientBoundary (n : ℕ) :
    ((singularChainsFunctor R).obj S.X₃).homology (n + 1) ⟶
      ((singularChainsFunctor R).obj S.X₁).homology n :=
  (singularChainsFunctor_map_shortExact R S hS).δ (n + 1) n rfl

/-- Six consecutive homology objects, with original coefficient maps, form an exact sequence. -/
@[stacks 0111 "Homology-sequence ingredient applied to actual ordinary singular chains"]
theorem singularCoefficientSequence_exact (n : ℕ) :
    (ComposableArrows.mk₅
      (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.f) (n + 1))
      (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.g) (n + 1))
      (singularCoefficientBoundary R S hS n)
      (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.f) n)
      (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.g) n)).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (singularChainsFunctor_map_shortExact R S hS) (n + 1) n rfl

include hS in
/-- The degree-zero rightmost map is epic, completing the low-degree exact tail. -/
theorem epi_singularHomologyZeroMap :
    Epi (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.g) 0) := by
  have : Epi ((singularChainsFunctor R).map S.g) :=
    (singularChainsFunctor_map_shortExact R S hS).epi_g
  apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
  intro j
  simp [ComplexShape.down]

/-- Vanishing of the middle coefficient homology identifies neighboring outer groups. -/
def singularCoefficientBoundaryIso (n : ℕ)
    (hi : IsZero (((singularChainsFunctor R).obj S.X₂).homology (n + 1)))
    (hj : IsZero (((singularChainsFunctor R).obj S.X₂).homology n)) :
    ((singularChainsFunctor R).obj S.X₃).homology (n + 1) ≅
      ((singularChainsFunctor R).obj S.X₁).homology n :=
  (singularChainsFunctor_map_shortExact R S hS).δIso (n + 1) n rfl hi hj

/-- The isomorphism keeps the native connecting map, including its sign convention. -/
theorem singularCoefficientBoundaryIso_hom (n : ℕ)
    (hi : IsZero (((singularChainsFunctor R).obj S.X₂).homology (n + 1)))
    (hj : IsZero (((singularChainsFunctor R).obj S.X₂).homology n)) :
    (singularCoefficientBoundaryIso R S hS n hi hj).hom =
      singularCoefficientBoundary R S hS n := rfl

/-- The connecting map commutes with actual smooth-site restriction. -/
theorem singularCoefficientBoundary_app_naturality (n : ℕ)
    {U V : (SmoothSite (Spec (.of R)))ᵒᵖ} (f : U ⟶ V) :
    (((singularChainsFunctor R).obj S.X₃).homology (n + 1)).map f ≫
        (singularCoefficientBoundary R S hS n).app V =
      (singularCoefficientBoundary R S hS n).app U ≫
        (((singularChainsFunctor R).obj S.X₁).homology n).map f :=
  (singularCoefficientBoundary R S hS n).naturality f

variable {S} in
/-- Functoriality under a genuine morphism of short exact coefficient sequences. -/
theorem singularCoefficientBoundary_naturality
    {T : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)} (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    singularCoefficientBoundary R S hS n ≫
        HomologicalComplex.homologyMap ((singularChainsFunctor R).map φ.τ₁) n =
      HomologicalComplex.homologyMap ((singularChainsFunctor R).map φ.τ₃) (n + 1) ≫
        singularCoefficientBoundary R T hT n :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((singularChainsFunctor R).mapShortComplex.map φ)
      (singularChainsFunctor_map_shortExact R S hS)
        (singularChainsFunctor_map_shortExact R T hT) (n + 1) n rfl

/-- Injective multiplication gives the actual native coefficient quotient sequence. -/
theorem singularReduction_shortExact
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] :
    (ShortComplex.cokernelSequence (m • 𝟙 P)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by change Mono (m • 𝟙 P); infer_instance

/-- The Bockstein for the native cokernel of injective coefficient multiplication.
The monomorphism is an explicit hypothesis; no flatness or torsion-freeness is hidden. -/
def singularBockstein
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] (n : ℕ) :
    ((singularChainsFunctor R).obj (cokernel (m • 𝟙 P))).homology (n + 1) ⟶
      ((singularChainsFunctor R).obj P).homology n :=
  singularCoefficientBoundary R (ShortComplex.cokernelSequence (m • 𝟙 P))
    (singularReduction_shortExact R P m) n

/-- The actual Bockstein image is annihilated by the original coefficient multiplication. -/
theorem singularBockstein_comp_multiplication
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] (n : ℕ) :
    singularBockstein R P m n ≫
      HomologicalComplex.homologyMap ((singularChainsFunctor R).map (m • 𝟙 P)) n = 0 :=
  (singularChainsFunctor_map_shortExact R _ (singularReduction_shortExact R P m)).δ_comp
    (n + 1) n rfl

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]

/-- The actual sheaf-valued connecting map after degreewise Nisnevich sheafification. -/
def nisnevichSingularCoefficientBoundary (n : ℕ) :
    ((nisnevichSingularChainsFunctor R).obj S.X₃).homology (n + 1) ⟶
      ((nisnevichSingularChainsFunctor R).obj S.X₁).homology n :=
  (nisnevichSingularChainsFunctor_map_shortExact R S hS).δ (n + 1) n rfl

/-- The native sheaf homologies and the actual coefficient maps form an exact sequence. -/
theorem nisnevichSingularCoefficientSequence_exact (n : ℕ) :
    (ComposableArrows.mk₅
      (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.f) (n + 1))
      (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.g) (n + 1))
      (nisnevichSingularCoefficientBoundary R S hS n)
      (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.f) n)
      (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.g) n)).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (nisnevichSingularChainsFunctor_map_shortExact R S hS) (n + 1) n rfl

include hS in
/-- The actual degree-zero map on Nisnevich singular homology sheaves is epic. -/
theorem epi_nisnevichSingularHomologyZeroMap :
    Epi (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.g) 0) := by
  have : Epi ((nisnevichSingularChainsFunctor R).map S.g) :=
    (nisnevichSingularChainsFunctor_map_shortExact R S hS).epi_g
  apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
  intro j
  simp [ComplexShape.down]

variable {S} in
/-- The sheaf-valued connecting morphism is natural in short exact coefficient sequences. -/
theorem nisnevichSingularCoefficientBoundary_naturality
    {T : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)} (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    nisnevichSingularCoefficientBoundary R S hS n ≫
        HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map φ.τ₁) n =
      HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map φ.τ₃) (n + 1) ≫
        nisnevichSingularCoefficientBoundary R T hT n :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((nisnevichSingularChainsFunctor R).mapShortComplex.map φ)
      (nisnevichSingularChainsFunctor_map_shortExact R S hS)
        (nisnevichSingularChainsFunctor_map_shortExact R T hT) (n + 1) n rfl

end AlgebraicSimplex
