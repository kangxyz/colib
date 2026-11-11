/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWords

/-!
# Recursion of the cast-preserving actual cone words

The original power equalities are transported through the actual cone functor. Equality
induction is performed in an abstract category before specialization, so no concrete cone
record is normalized to erase its casts. The local geometric map remains unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange FiniteConeTopology

private theorem conjugate_map_comp {D : Type u} [Category.{v} D] (C : D ⥤ D)
    {X Y : D} (h : X = Y) (a : X ⟶ X) (b : C.obj X ⟶ C.obj X) :
    eqToHom (congrArg C.obj h).symm ≫ (C.map a ≫ b) ≫ eqToHom (congrArg C.obj h) =
      C.map (eqToHom h.symm ≫ a ≫ eqToHom h) ≫
        (eqToHom (congrArg C.obj h).symm ≫ b ≫ eqToHom (congrArg C.obj h)) := by
  subst Y
  simp

/-- The actual cone endofunctor acts by the already used complete cone map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWordRecursion.lean:34"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem coneFunctor_map {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    coneFunctor.map f = ConeTrack.map squareFunctor f := rfl

/-- The zeroth accumulated word remains identity after its original equality transports. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWordRecursion.lean:38"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem wordAt_zero_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (wordAt 0 F).hom = 𝟙 F := by
  simp only [wordAt, word, Functor.FixedWords.fixedWord, Iso.trans_hom,
    Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.app_hom, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, eqToHom_trans]
  rfl

/-- The initial insertion remains identity on the original first cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWordRecursion.lean:46"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem betaAt_zero_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (betaAt 0 F).hom = 𝟙 (iterate squareFunctor 1 F) := by
  simp [betaAt, beta, Functor.FixedWords.beta]

/-- The accumulated word recursion retains the full original power transports. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWordRecursion.lean:51"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem wordAt_succ_hom (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (wordAt (i + 1) F).hom =
      ConeTrack.map squareFunctor (wordAt i F).hom ≫ (betaAt i F).hom := by
  unfold wordAt betaAt
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.app_hom]
  erw [show (word (i + 1)).hom.app F =
    coneFunctor.map ((word i).hom.app F) ≫ (beta i).hom.app F from
      Functor.FixedWords.fixedWord_succ_hom_app coneFunctor permutationFunctorIso i F]
  exact conjugate_map_comp coneFunctor (power_obj i F) ((word i).hom.app F)
    ((beta i).hom.app F)

end KTheory.Bass.GeometricConeFixedWords
