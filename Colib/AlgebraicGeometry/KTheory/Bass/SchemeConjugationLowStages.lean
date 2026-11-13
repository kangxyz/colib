/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTransitions
public import
  Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWordRecursion

/-!
Source: `Quillen/KTheory/Bass/SchemeConjugationLowStages.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The first two actual normalized conjugations

The first conjugation is identity. The second retains the original double-loop
transpose and the actual geometric cone permutation, including its complete
diagram equality transports. No assertion about its action on Bass quotient
classes follows from the second formula alone.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Topology
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteLoopWords
open KTheory.Bass.GeometricConeFixedWords
open KTheory.Bass.FiniteConeTopology

universe u w

namespace KTheory.Bass.SchemeNaturalSeed

/-- The original first cone word remains identity after both equality transports. -/
theorem wordAt_one_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (wordAt 1 F).hom = 𝟙 (iterate squareFunctor 1 F) := by
  rw [wordAt_succ_hom, wordAt_zero_hom, betaAt_zero_hom]
  change GeometricConeInterchange.coneFunctor.map (𝟙 F) ≫ 𝟙 _ = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The first actual normalized conjugation is identity as a complete diagram map. -/
theorem conjugatingIso_one_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (conjugatingIso 1 F).hom = 𝟙 (NormalizedStageMap.normalized squareFunctor 1 F) := by
  rw [conjugatingIso_hom, wordAt_one_hom, loopMap_id]
  rw [Category.comp_id]
  rfl

/-- The geometric part of the second word is the original permutation with its full casts. -/
theorem wordAt_two_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (wordAt 2 F).hom =
      eqToHom (power_obj 2 F).symm ≫
        (GeometricConeInterchange.permutationNatIso F).hom ≫ eqToHom (power_obj 2 F) := by
  simp only [wordAt, word_two, Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.hom]
  rfl

/-- The second actual conjugation keeps both the transpose and the original geometric map. -/
theorem conjugatingIso_two_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (conjugatingIso 2 F).hom =
      (transposeIso (iterate squareFunctor 2 F)).hom ≫
        loopMap 2 (eqToHom (power_obj 2 F).symm ≫
          (GeometricConeInterchange.permutationNatIso F).hom ≫
            eqToHom (power_obj 2 F)) := by
  rw [conjugatingIso_hom, wordAt_two_hom]
  rfl

end KTheory.Bass.SchemeNaturalSeed
