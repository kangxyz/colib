/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Normalized Moore complexes and additive functors

The normalized Moore complex splits Mathlib's idempotent on the alternating
face map complex. An additive functor preserves this idempotent. Comparing the
two splittings identifies the normalized complexes and their inclusions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category

namespace AlgebraicTopology

open AlgebraicTopology.DoldKan

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]

private def normalizedMooreRetraction (A : Type*) [Category* A] [Abelian A] :
    alternatingFaceMapComplex A ⟶ normalizedMooreComplex A where
  app := PInftyToNormalizedMooreComplex
  naturality _ _ f := PInftyToNormalizedMooreComplex_naturality f

private theorem inclusionOfMooreComplex_comp_retraction :
    inclusionOfMooreComplex A ≫ normalizedMooreRetraction A = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  exact (splitMonoInclusionOfMooreComplexMap X).id

private theorem normalizedMooreRetraction_comp_inclusion :
    normalizedMooreRetraction A ≫ inclusionOfMooreComplex A = natTransPInfty A := by
  apply NatTrans.ext
  funext X
  exact PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X

variable (G : A ⥤ B) [G.Additive]

private theorem map_natTransPInfty_comp_hom :
    Functor.whiskerRight (natTransPInfty A) (G.mapHomologicalComplex (ComplexShape.down ℕ)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom ≫
        Functor.whiskerLeft ((SimplicialObject.whiskering A B).obj G) (natTransPInfty B) := by
  apply NatTrans.ext
  funext X
  ext n
  simp

/-- The normalized Moore complex commutes naturally with applying an additive
functor degreewise. The comparison uses the splittings of the same projection
in the alternating face map complex. -/
@[no_expose]
def normalizedMooreComplexCompMapHomologicalComplexIso :
    normalizedMooreComplex A ⋙ G.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      (SimplicialObject.whiskering A B).obj G ⋙ normalizedMooreComplex B := by
  let K := G.mapHomologicalComplex (ComplexShape.down ℕ)
  let S := (SimplicialObject.whiskering A B).obj G
  let e := alternatingFaceMapComplexCompMapHomologicalComplexIso G
  let i₁ := Functor.whiskerRight (inclusionOfMooreComplex A) K ≫ e.hom
  let r₁ := e.inv ≫ Functor.whiskerRight (normalizedMooreRetraction A) K
  let i₂ := Functor.whiskerLeft S (inclusionOfMooreComplex B)
  let r₂ := Functor.whiskerLeft S (normalizedMooreRetraction B)
  have h₁ : i₁ ≫ r₁ = 𝟙 _ := by
    simp only [i₁, r₁, assoc, Iso.hom_inv_id_assoc, ← Functor.whiskerRight_comp,
      inclusionOfMooreComplex_comp_retraction, Functor.whiskerRight_id']
  have h₂ : i₂ ≫ r₂ = 𝟙 _ := by
    simp only [i₂, r₂, ← Functor.whiskerLeft_comp, inclusionOfMooreComplex_comp_retraction,
      Functor.whiskerLeft_id']
  have h : r₁ ≫ i₁ = r₂ ≫ i₂ := by
    calc
      r₁ ≫ i₁ =
          e.inv ≫ Functor.whiskerRight
            (normalizedMooreRetraction A ≫ inclusionOfMooreComplex A) K ≫ e.hom := by
        simp only [r₁, i₁, Functor.whiskerRight_comp, assoc]
      _ = r₂ ≫ i₂ := by
        rw [normalizedMooreRetraction_comp_inclusion, map_natTransPInfty_comp_hom]
        change e.inv ≫ e.hom ≫ S.whiskerLeft (natTransPInfty B) = r₂ ≫ i₂
        simp only [Iso.inv_hom_id_assoc, r₂, i₂, ← Functor.whiskerLeft_comp,
          normalizedMooreRetraction_comp_inclusion]
  have hi : (i₁ ≫ r₂) ≫ i₂ = i₁ := by
    rw [assoc, ← h, ← assoc, h₁, id_comp]
  have hr : (i₂ ≫ r₁) ≫ i₁ = i₂ := by
    rw [assoc, h, ← assoc, h₂, id_comp]
  exact ⟨i₁ ≫ r₂, i₂ ≫ r₁, by rw [← assoc, hi, h₁], by rw [← assoc, hr, h₂]⟩

/-- The normalized comparison intertwines the canonical inclusions into the
alternating face map complex. -/
@[reassoc]
theorem normalizedMooreComplexCompMapHomologicalComplexIso_hom_comp_inclusionOfMooreComplex :
    (normalizedMooreComplexCompMapHomologicalComplexIso G).hom ≫
        Functor.whiskerLeft ((SimplicialObject.whiskering A B).obj G) (inclusionOfMooreComplex B) =
      Functor.whiskerRight (inclusionOfMooreComplex A)
        (G.mapHomologicalComplex (ComplexShape.down ℕ)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom := by
  let K := G.mapHomologicalComplex (ComplexShape.down ℕ)
  let S := (SimplicialObject.whiskering A B).obj G
  let e := alternatingFaceMapComplexCompMapHomologicalComplexIso G
  change ((Functor.whiskerRight (inclusionOfMooreComplex A) K ≫ e.hom) ≫
      Functor.whiskerLeft S (normalizedMooreRetraction B)) ≫
      Functor.whiskerLeft S (inclusionOfMooreComplex B) = _
  have h : inclusionOfMooreComplex A ≫ natTransPInfty A = inclusionOfMooreComplex A := by
    apply NatTrans.ext
    funext X
    exact inclusionOfMooreComplexMap_comp_PInfty X
  simp only [assoc, ← Functor.whiskerLeft_comp, normalizedMooreRetraction_comp_inclusion]
  rw [← map_natTransPInfty_comp_hom, ← assoc, ← Functor.whiskerRight_comp, h]

end AlgebraicTopology
