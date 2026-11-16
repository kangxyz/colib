/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueKEquivalence
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectShiftSign
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic

/-! # Literal direct image and shift on flasque perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Waldhausen
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

variable {X Y : Scheme.{u}}

local notation "W" X =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X))

private lemma exact_of_shortExact (F : Obj X ⥤ Obj Y) [F.Additive]
    (hF : IsExact (waldhausen X).cof (waldhausen X).weq (W Y).cof (W Y).weq
      (F ⋙ perfectInclusion Y))
    (hs : ∀ (S : ShortComplex (Obj X)), (S.map (objects X).ι).ShortExact →
      ((S.map F).map (objects Y).ι).ShortExact) :
    IsExact (waldhausen X).cof (waldhausen X).weq (waldhausen Y).cof (waldhausen Y).weq F := by
  let E : ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (objects X))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
        (objects Y)) := ⟨F, hs⟩
  exact { zero h := F.map_isZero h
          cofibration f hf := E.map_inflation f hf
          weak f hf := hF.weak f hf
          pushout hi h := E.map_isPushout hi h }

variable (f : X ⟶ Y) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]

local notation "D" => Functor.mapHomologicalComplex (pushforward f) (ComplexShape.up ℤ)

/-- Actual direct image lands in the existing termwise flasque perfect subcategory. -/
def flasquePerfectPushforward : Obj X ⥤ Obj Y :=
  ObjectProperty.lift (objects Y) ((objects X).ι ⋙ D) (fun K => by
    refine ⟨⟨((perfectPushforward f).obj K).property, ?_⟩, fun n => ?_⟩
    · obtain ⟨a, ha⟩ := K.property.1.2
      let := ha
      refine ⟨a, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact (pushforward f).map_isZero (K.obj.isZero_of_isStrictlyGE a i hi)
    · exact Stacks.RelativeLeray.isFlasque_modulePushforward (Scheme.forgetToRingedSpace.map f)
        (K.obj.X n) (K.property.2 n))

instance flasquePerfectPushforward_additive : (flasquePerfectPushforward f).Additive where
  map_add := by
    intro K L a b
    apply ObjectProperty.hom_ext
    exact (D).map_add (f := a.hom) (g := b.hom)

/-- Actual flasque direct image is exact by its inclusion into the perfect category. -/
theorem flasquePerfectPushforward_exact :
    IsExact (waldhausen X).cof (waldhausen X).weq (waldhausen Y).cof (waldhausen Y).weq
      (flasquePerfectPushforward f) :=
  exact_of_shortExact _ (perfectPushforward_exact f)
    (fun _ h => perfectPushforward_shortExact f h)

/-- The standard cochain shift restricted to existing termwise flasque perfect complexes. -/
def flasquePerfectShift (Y : Scheme.{u}) (m : ℤ) : Obj Y ⥤ Obj Y :=
  ObjectProperty.lift (objects Y) ((objects Y).ι ⋙ shiftFunctor _ m) (fun K => by
    refine ⟨⟨isPerfectComplex_shift Y.toRingedSpace _ K.property.1.1 m, ?_⟩, fun n => ?_⟩
    · obtain ⟨a, ha⟩ := K.property.1.2
      let := ha
      exact ⟨a - m, K.obj.isStrictlyGE_shift a m (a - m) (by omega)⟩
    · exact TopCat.Sheaf.IsFlasque.of_iso
        ((SheafOfModules.toSheaf (structureSheafRing Y.toRingedSpace)).mapIso
          (K.obj.shiftFunctorObjXIso m n (n + m) rfl).symm) (K.property.2 (n + m)))

instance flasquePerfectShift_additive (Y : Scheme.{u}) (m : ℤ) :
    (flasquePerfectShift Y m).Additive where
  map_add := by
    intro K L a b
    apply ObjectProperty.hom_ext
    exact (shiftFunctor (CochainComplex Y.Modules ℤ) m).map_add (f := a.hom) (g := b.hom)

/-- The literal shift on termwise flasque perfect complexes is Waldhausen exact. -/
theorem flasquePerfectShift_exact (Y : Scheme.{u}) (m : ℤ) :
    IsExact (waldhausen Y).cof (waldhausen Y).weq (waldhausen Y).cof (waldhausen Y).weq
      (flasquePerfectShift Y m) :=
  exact_of_shortExact _
    ((perfectInclusion_exact Y).comp (perfectShift_exact Y.toRingedSpace m))
    (fun _ h => h.map_of_exact (shiftFunctor (CochainComplex Y.Modules ℤ) m))

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
