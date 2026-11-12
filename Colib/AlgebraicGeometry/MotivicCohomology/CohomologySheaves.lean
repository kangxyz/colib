/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Hypercohomology
public import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Cohomology sheaves of the motivic complex

In degree `q-r`, the cohomology sheaf of the canonical signed motivic complex
is Nisnevich sheafification of the degree-`r` homology of the raw transfer
singular complex of the reduced torus. The comparison uses the actual signed
placement isomorphism and exact transfer sheafification. Forgetting transfers
gives the ordinary Nisnevich sheafification of the graph restriction of the
same homology presheaf. Both cohomology sheaves vanish above the weight.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The actual degree-`q-r` motivic cohomology sheaf is sheafified Suslin
homology in chain degree `r`, with its transfers. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:135-141"
  "adaptation" "Exact transfer sheafification and the canonical signed motivic shift"]
def motivicComplexHomologyIso (q r : ℕ) :
    (motivicComplex k q).homology ((q : ℤ) - r) ≅
      (nisnevichSheafify k).obj ((singularComplex (reducedTorus k q)).homology r) :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) ((q : ℤ) - r)).mapIso
      (motivicComplexPlacementIso k q).symm ≪≫
    ((singularCochainComplex (reducedTorus k q) q).sc ((q : ℤ) - r)).mapHomologyIso
      (nisnevichSheafify k) ≪≫
    (nisnevichSheafify k).mapIso
      ((singularComplex (reducedTorus k q)).extendHomologyIso
        (ComplexShape.embeddingUpIntLE (q : ℤ)) (j := r) rfl)

/-- The transfer cohomology sheaf above the weight is zero. -/
theorem isZero_motivicComplex_homology (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicComplex k q).homology i) :=
  ((motivicComplex k q).sc i).isZero_homology_of_isZero_X₂
    (isZero_motivicComplex_X k q i hi)

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

/-- Forgetting transfers commutes with cohomology of the actual motivic complex. -/
def motivicSheafComplexHomologyUnderlyingIso (q : ℕ) (i : ℤ) :
    (motivicSheafComplex k q).homology i ≅
      (SheafWithTransfers.toSheaf k).obj ((motivicComplex k q).homology i) :=
  ((motivicComplex k q).sc i).mapHomologyIso (SheafWithTransfers.toSheaf k)

/-- The ordinary degree-`q-r` motivic cohomology sheaf is ordinary Nisnevich
sheafification of the graph restriction of degree-`r` Suslin homology. -/
def motivicSheafComplexHomologyIso (q r : ℕ) :
    (motivicSheafComplex k q).homology ((q : ℤ) - r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj
          ((toPresheaf k).obj ((singularComplex (reducedTorus k q)).homology r)) :=
  motivicSheafComplexHomologyUnderlyingIso k q ((q : ℤ) - r) ≪≫
    (SheafWithTransfers.toSheaf k).mapIso (motivicComplexHomologyIso k q r) ≪≫
    ((nisnevichSheafificationUnderlyingIso k).app
      ((singularComplex (reducedTorus k q)).homology r)).symm

/-- The ordinary motivic cohomology sheaf above the weight is zero. -/
theorem isZero_motivicSheafComplex_homology (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicSheafComplex k q).homology i) :=
  (motivicSheafComplexHomologyUnderlyingIso k q i).isZero_iff.mpr
    ((SheafWithTransfers.toSheaf k).map_isZero (isZero_motivicComplex_homology k q i hi))

end AlgebraicGeometry.PresheafWithTransfers
