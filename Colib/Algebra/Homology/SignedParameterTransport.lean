/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.SignedParameterConjugation
public import Colib.Algebra.Homology.ArrowCompositionData
public import Colib.CategoryTheory.Shift.ParameterSignedTransport

/-! # Signed parameter transport retaining an arbitrary native comparison tail

The comparison transformation is one-way. The composite data stores its full tail
before interpreting the resulting arrow; no comparison is inverted.
-/
@[expose] public noncomputable section
open CategoryTheory
open CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D]
  [HasShift C ℤ] [HasShift D ℤ]
  (E : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D)
  [E.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  (τ : F ⋙ E ⟶ E ⋙ G) [NatTrans.CommShift τ ℤ]

/-- The named signed arrow obeys the native one-way parameter transport square. -/
theorem signedParameterArrow_transport {M N X Y : C} {M' N' : D}
    (f : M ⟶ F.obj N) (g : M' ⟶ G.obj N')
    (a : E.obj M ≅ M') (b : E.obj N ≅ N')
    (h : E.map f ≫ τ.app N ≫ G.map b.hom = a.hom ≫ g)
    (t s : ℤ) (hs : t + 1 = s)
    (θ : X ≅ (shiftFunctor C s).obj M) (ψ : Y ≅ (shiftFunctor C t).obj N) :
    E.map (signedParameterArrow F f t s hs θ ψ) ≫
      τ.app ((shiftFunctor C (1 : ℤ)).obj Y) ≫
      G.map ((E.commShiftIso (1 : ℤ)).hom.app Y) =
    signedParameterArrow G g t s hs
      (E.mapIso θ ≪≫ (E.commShiftIso s).app M ≪≫ (shiftFunctor D s).mapIso a)
      (E.mapIso ψ ≪≫ (E.commShiftIso t).app N ≪≫ (shiftFunctor D t).mapIso b) :=
  parameter_square_signed E F G τ f g a b h t s hs θ ψ

/-- Store a signed arrow and its original comparison tail as separate factors. -/
def signedParameterCompositeData {M N X Y Z : D} (g : M ⟶ G.obj N)
    (t s : ℤ) (hs : t + 1 = s)
    (a : X ≅ (shiftFunctor D s).obj M) (b : Y ≅ (shiftFunctor D t).obj N)
    (tail : G.obj ((shiftFunctor D (1 : ℤ)).obj Y) ⟶ Z) : ArrowCompositionData D :=
  ⟨Arrow.mk (signedParameterArrow G g t s hs a b), Arrow.mk tail, rfl⟩

/-- Interpreting the data composes with exactly the stored native tail. -/
theorem signedParameterCompositeData_hom {M N X Y Z : D} (g : M ⟶ G.obj N)
    (t s : ℤ) (hs : t + 1 = s)
    (a : X ≅ (shiftFunctor D s).obj M) (b : Y ≅ (shiftFunctor D t).obj N)
    (tail : G.obj ((shiftFunctor D (1 : ℤ)).obj Y) ⟶ Z) :
    (signedParameterCompositeData G g t s hs a b tail).toArrow.hom =
      signedParameterArrow G g t s hs a b ≫ tail := by
  simp [signedParameterCompositeData, ArrowCompositionData.toArrow, arrowPostcompose]
