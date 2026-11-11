/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWordRecursion

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

private theorem conjugate_local_map {D : Type u} [Category.{v} D] (C : D ⥤ D)
    (P : C ⋙ C ≅ C ⋙ C) {X Y : D} (h : X = Y) (b : C.obj X ⟶ C.obj X) :
    eqToHom (congrArg (fun Z => C.obj (C.obj Z)) h).symm ≫
        (P.hom.app X ≫ C.map b) ≫ eqToHom (congrArg (fun Z => C.obj (C.obj Z)) h) =
      P.hom.app Y ≫
        C.map (eqToHom (congrArg C.obj h).symm ≫ b ≫ eqToHom (congrArg C.obj h)) := by
  subst Y
  simp

/-- The insertion recursion uses the same local geometric map on the original cone iterate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeBetaRecursion.lean:35"
  "adaptation" "Original insertion-word recursion with complete power transports."]
theorem betaAt_succ_hom (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (betaAt (i + 1) F).hom =
      (permutationNatIso (iterate squareFunctor i F)).hom ≫
        ConeTrack.map squareFunctor (betaAt i F).hom := by
  unfold betaAt
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.app_hom]
  erw [show (beta (i + 1)).hom.app F =
    permutationFunctorIso.hom.app ((Functor.FixedWords.power coneFunctor i).obj F) ≫
      coneFunctor.map ((beta i).hom.app F) from
        Functor.FixedWords.beta_succ_hom_app coneFunctor permutationFunctorIso i F]
  have h := conjugate_local_map coneFunctor permutationFunctorIso (power_obj i F)
    ((beta i).hom.app F)
  dsimp only [permutationFunctorIso, NatIso.ofComponents] at h ⊢
  dsimp only [iterate, Functor.FixedWords.power, Functor.comp_obj] at h ⊢
  erw [← coneFunctor_map]
  exact h

end KTheory.Bass.GeometricConeFixedWords
