/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.EndotransformationContractionStructure



/-!
# Naturality of the original endotransformation contraction

Chosen-zero preservation and the universal properties of the actual zero objects identify the
original zero endotransformation under strict exact whiskering. The composition triangle and
uniform time operations then identify the existing cancellation expression pointwise. No new
contraction is chosen. Both homotopy times remain independent; degree zero retains its original
based-loop coordinate through the imported whole-level naturality statements.
-/
@[expose] public section

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology CategoryTheory.Functor Topology.LoopPrespectrum
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory SSet
universe u

namespace CategoryTheory.Waldhausen.IteratedS

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
variable {V' W' : WideSubcategory preservesZero.{u}} {F' : V' ⟶ W'}

/-- The original scalar square transfers exactly the original weakness witness. -/
private theorem originalCoefficientConjugate_weak
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm)) :
    ∀ X, U.obj.waldhausen.weq
      ((eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm)).app X) := by
  intro X
  rw [← he]
  exact b.hom.isExact.weak _ (hη X)

/-- This is exactly the original prewhiskering, with its composite Model endpoint displayed. -/
private def coefficientPrewhiskerTyped {V T U : WideSubcategory preservesZero.{u}} (a : V ⟶ T) (G
  : T ⟶ U)
    (θ : G.hom.toFunctor ⟶ G.hom.toFunctor) : (a ≫ G).hom.toFunctor ⟶ (a ≫ G).hom.toFunctor :=
  whiskerLeft a.hom.toFunctor θ

/-- Naming the endpoint conversion changes no transformation. -/
private theorem coefficientPrewhiskerTyped_eq {V T U : WideSubcategory preservesZero.{u}} (a : V ⟶
  T) (G : T ⟶ U)
    (θ : G.hom.toFunctor ⟶ G.hom.toFunctor) :
    coefficientPrewhiskerTyped a G θ = whiskerLeft a.hom.toFunctor θ := rfl

/-- The named transformation has the original component weakness witness. -/
private theorem coefficientPrewhiskerTyped_weak {V T U : WideSubcategory preservesZero.{u}} (a : V
  ⟶ T) (G : T ⟶ U)
    (θ : G.hom.toFunctor ⟶ G.hom.toFunctor) (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X)) :
    ∀ X, U.obj.waldhausen.weq ((coefficientPrewhiskerTyped a G θ).app X) :=
  fun X ↦ hθ (a.hom.toFunctor.obj X)

/-- The same original coefficient square transfers weakness of the named transformation. -/
private theorem coefficientPrewhiskerTyped_conjugate_weak
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm)) :
    ∀ X, U.obj.waldhausen.weq
      ((eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ coefficientPrewhiskerTyped a G θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm)).app X) :=
  originalCoefficientConjugate_weak
    (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he

/-- This is exactly the original postwhiskering at the displayed Model composite. -/
private def coefficientPostwhiskerTyped {V W U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (b
  : W ⟶ U)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) : (F ≫ b).hom.toFunctor ⟶ (F ≫ b).hom.toFunctor :=
  whiskerRight η b.hom.toFunctor

/-- Naming the endpoint conversion changes no transformation. -/
private theorem coefficientPostwhiskerTyped_eq {V W U : WideSubcategory preservesZero.{u}} (F : V
  ⟶ W) (b : W ⟶ U)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) :
    coefficientPostwhiskerTyped F b η = whiskerRight η b.hom.toFunctor := rfl

/-- The named transformation retains the original exact-image weakness proof. -/
private theorem coefficientPostwhiskerTyped_weak {V W U : WideSubcategory preservesZero.{u}} (F :
  V ⟶ W) (b : W ⟶ U)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ X, W.obj.waldhausen.weq (η.app X)) :
    ∀ X, U.obj.waldhausen.weq ((coefficientPostwhiskerTyped F b η).app X) :=
  fun X ↦ b.hom.isExact.weak _ (hη X)

/-- The original coefficient square is unchanged when its two endpoint conversions are named. -/
private theorem coefficientWhiskerTyped_square
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm)) :
    coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫
        coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
          eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm) := he

/-- Actual coefficient transport, with the same original two composites and weak-zero proofs. -/
private theorem originalContractionCoefficientTransportTyped
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
    (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))
    (hz' : ∀ X, U.obj.waldhausen.weq ((zeroEndotransformation G).app X))
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫
        coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
      (coefficientPrewhiskerTyped_conjugate_weak
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
      (zeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) =
    (prespectrumEndotransformationContraction (V := V) (W := U) (a ≫ G)
      (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
      (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
      (zeroEndotransformation_precomp_weak
        (V := T) (W := U) (T := V) G hz' a)).level n (r, (s, x)) :=
  prespectrumEndotransformationContraction_transport_level
    (V := V) (W := U) (F := F ≫ b) (F' := a ≫ G) h
    (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
    (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
    (coefficientPrewhiskerTyped_conjugate_weak
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
    (zeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)
    (zeroEndotransformation_precomp_weak
        (V := T) (W := U) (T := V) G hz' a) n r s x

/-- The original scalar square compares the chosen contractions at identical independent times. -/
private theorem originalCoefficientEndotransformationEqTyped
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
      (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
      (zeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) =
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫
        coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
          eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
      (coefficientPrewhiskerTyped_conjugate_weak
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
      (zeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) :=
  prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := U) (F := F ≫ b) (F' := F ≫ b) rfl
    (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
    (eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫
      coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
    (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
    (coefficientPrewhiskerTyped_conjugate_weak
      (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
    (zeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (zeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (heq_of_eq (coefficientWhiskerTyped_square
      (V := V) (W := W) (T := T) (U := U) F G a b h η θ he)) n r s x

/-- The typed postwhiskering retains the original postcomposition point at both times. -/
private theorem originalContractionPostTyped
    {V W U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (b : W ⟶ U)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
      (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
      (zeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) =
      (prespectrumMap (V := W) (W := U) b).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) := by
  have he := prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := U) (F := F ≫ b) (F' := F ≫ b) rfl
    (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
    (whiskerRight η b.hom.toFunctor)
    (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
    (fun X : V.obj.Obj ↦ b.hom.isExact.weak _ (hη X))
    (zeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (zeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (heq_of_eq (coefficientPostwhiskerTyped_eq (V := V) (W := W) (U := U) F b η))
    n r s x
  exact he.trans (prespectrumEndotransformationContraction_postcomp_level
    (V := V) (W := W) (T := U) F η hη hz b
    (zeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b) n r s x)

/-- The typed prewhiskering retains the original precomposition point at both times. -/
private theorem originalContractionPreTyped
    {V T U : WideSubcategory preservesZero.{u}} (a : V ⟶ T) (G : T ⟶ U)
    (θ : G.hom.toFunctor ⟶ G.hom.toFunctor) (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
    (hz : ∀ X, U.obj.waldhausen.weq ((zeroEndotransformation G).app X))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (a ≫ G)
      (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
      (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
      (zeroEndotransformation_precomp_weak
        (V := T) (W := U) (T := V) G hz a)).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction G θ hθ hz).level n
        (r, (s, (prespectrumMap (V := V) (W := T) a).map n x)) := by
  have he := prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := U) (F := a ≫ G) (F' := a ≫ G) rfl
    (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
    (whiskerLeft a.hom.toFunctor θ)
    (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
    (fun X : V.obj.Obj ↦ hθ (a.hom.toFunctor.obj X))
    (zeroEndotransformation_precomp_weak (V := T) (W := U) (T := V) G hz a)
    (fun X : V.obj.Obj ↦ hz (a.hom.toFunctor.obj X))
    (heq_of_eq (coefficientPrewhiskerTyped_eq (V := V) (T := T) (U := U) a G θ)) n r s x
  exact he.trans (prespectrumEndotransformationContraction_precomp_level
    (V := T) (W := U) (T := V) G θ hθ hz a n r s x)

/-- The original strict coefficient square and scalar equation preserve the same contraction.
All equality-induced transports and both original comparison times are retained. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:848"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_naturality
    {V W T U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
    (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))
    (hz' : ∀ X, U.obj.waldhausen.weq ((zeroEndotransformation G).app X))
    (he : whiskerRight η b.hom.toFunctor =
      eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫ whiskerLeft a.hom.toFunctor θ ≫
        eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) =
      (prespectrumEndotransformationContraction G θ hθ hz').level n
        (r, (s, (prespectrumMap a).map n x)) := by
  calc
    _ = (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
        (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
        (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
        (zeroEndotransformation_postcomp_weak
          (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) :=
      (originalContractionPostTyped (V := V) (W := W) (U := U) F b η hη hz n r s x).symm
    _ = (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
        (eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h) ≫
          coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
            eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) h.symm))
        (coefficientPrewhiskerTyped_conjugate_weak
          (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
        (zeroEndotransformation_postcomp_weak
          (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) :=
      originalCoefficientEndotransformationEqTyped
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη hz he n r s x
    _ = (prespectrumEndotransformationContraction (V := V) (W := U) (a ≫ G)
        (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
        (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
        (zeroEndotransformation_precomp_weak
          (V := T) (W := U) (T := V) G hz' a)).level n (r, (s, x)) :=
      originalContractionCoefficientTransportTyped
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη hθ hz hz' he n r s x
    _ = _ := originalContractionPreTyped (V := V) (T := T) (U := U) a G θ hθ hz' n r s x

end CategoryTheory.Waldhausen.IteratedS

