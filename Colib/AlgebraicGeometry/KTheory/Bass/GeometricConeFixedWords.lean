/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Endofunctor.FixedWords
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality
public import Colib.KTheory.Bass.FiniteConeTopology

/-!
# Fixed words of the actual geometric two-cone isomorphism

The actual unlooped cone functor and its geometric square isomorphism instantiate the
specified finite words. Their powers are identified with the same finite cone iterates
used by the topology and action constructions. All complete diagram equality casts are
retained. No seed compatibility, external-unit cube, braid law, or tower map is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange FiniteConeTopology

/-- The actual local geometric isomorphism supplies the prescribed insertion word. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:29"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
def beta (i : ℕ) : Functor.FixedWords.power coneFunctor.{u,w} (i + 1) ≅
    Functor.FixedWords.power coneFunctor (i + 1) :=
  Functor.FixedWords.beta coneFunctor permutationFunctorIso i

/-- The accumulated geometric word uses precisely the fixed generic recursion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:34"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
def word (i : ℕ) : Functor.FixedWords.power coneFunctor.{u,w} i ≅
    Functor.FixedWords.power coneFunctor i :=
  Functor.FixedWords.fixedWord coneFunctor permutationFunctorIso i

/-- The complete object diagram is the same finite unlooped cone iterate as before. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:39"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem power_obj (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (Functor.FixedWords.power coneFunctor i).obj F = iterate squareFunctor i F := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change ConeTrack.diagram squareFunctor
      ((Functor.FixedWords.power coneFunctor i).obj F) =
      ConeTrack.diagram squareFunctor (iterate squareFunctor i F)
    exact congrArg (ConeTrack.diagram squareFunctor) ih

/-- The insertion word on the previous finite-cone diagrams retains its equality transports. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:50"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
def betaAt (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    iterate squareFunctor (i + 1) F ≅ iterate squareFunctor (i + 1) F :=
  (eqToIso (power_obj (i + 1) F)).symm ≪≫ (beta i).app F ≪≫
    eqToIso (power_obj (i + 1) F)

/-- The accumulated word on the previous finite-cone diagrams retains both full casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:56"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
def wordAt (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    iterate squareFunctor i F ≅ iterate squareFunctor i F :=
  (eqToIso (power_obj i F)).symm ≪≫ (word i).app F ≪≫ eqToIso (power_obj i F)

/-- The second word is exactly the already constructed geometric square isomorphism. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:61"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem word_two : word.{u, w} 2 = permutationFunctorIso :=
  Functor.FixedWords.fixedWord_two coneFunctor permutationFunctorIso

/-- The third word has the prescribed three factors as whole strict diagram maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeFixedWords.lean:65"
  "adaptation" "Original fixed geometric word recursion with complete equality transports."]
theorem word_three_hom_app (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (word 3).hom.app F =
      coneFunctor.map (permutationNatIso F).hom ≫
      (permutationNatIso (coneFunctor.obj F)).hom ≫
      coneFunctor.map (permutationNatIso F).hom :=
  Functor.FixedWords.fixedWord_three_hom_app coneFunctor permutationFunctorIso F

end KTheory.Bass.GeometricConeFixedWords
