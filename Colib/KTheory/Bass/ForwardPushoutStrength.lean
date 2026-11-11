/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.PointwisePushout
public import Colib.KTheory.Bass.StrictDiagramHomotopy

/-! # Forward Bass comparison for the actual pointwise pushout

The unchanged whole overlap and its original endpoint casts define the forward comparison.
No inverse comparison or extra compatibility hypothesis is introduced.
The pinned original is an adopted independent reconstruction after workspace loss,
not historical byte recovery.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.PushoutStrength
variable {C : Type u} [Category.{v} C]
  {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)

/-- The unchanged left inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:58"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
def left : F₁ ⟶ pushout f g where
  app X := HomotopyPushout.inl (f.app X) (g.app X)
  naturality _X _Y k := (HomotopyPushout.inl_map _ _ _ _ _ _ _
    (f.naturality k).symm (g.naturality k).symm).symm

/-- The unchanged right inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:64"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
def right : F₂ ⟶ pushout f g where
  app X := HomotopyPushout.inr (f.app X) (g.app X)
  naturality _X _Y k := (HomotopyPushout.inr_map _ _ _ _ _ _ _
    (f.naturality k).symm (g.naturality k).symm).symm

/-- The original whole overlap, with transformation endpoints. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:70"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
def glue (X : C) : Homotopy ((f ≫ left f g).app X) ((g ≫ right f g).app X) :=
  HomotopyPushout.glue (f.app X) (g.app X)

/-- The original overlap is coefficient-natural at the identical time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:74"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
theorem glue_naturality {X Y : C} (k : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (F₀.obj X).space n) :
    ((pushout f g).map k).map n ((glue f g X).level n (r, x)) =
      (glue f g Y).level n (r, (F₀.map k).map n x) := rfl

variable (Q : C ⥤ Arrow (Arrow C))

/-- Bass acts on the entire original overlap; only endpoint witnesses are cast. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:82"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
def bassGlue (X : C) :
    Homotopy ((((strictDiagramFunctor Q).map f).app X) ≫
        (((strictDiagramFunctor Q).map (left f g)).app X))
      ((((strictDiagramFunctor Q).map g).app X) ≫
        (((strictDiagramFunctor Q).map (right f g)).app X)) :=
  (strictDiagramMapHomotopy (glue f g) (glue_naturality f g) Q X).cast
    (congrArg (fun a => a.app X) ((strictDiagramFunctor Q).map_comp f (left f g)))
    (congrArg (fun a => a.app X) ((strictDiagramFunctor Q).map_comp g (right f g)))

/-- The original quotient descent defining the forward comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:92"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
def comparison (X : C) :
    HomotopyPushout.prespectrum (((strictDiagramFunctor Q).map f).app X)
      (((strictDiagramFunctor Q).map g).app X) ⟶
        (((strictDiagramFunctor Q).obj (pushout f g)).obj X) :=
  HomotopyPushout.desc _ _ (((strictDiagramFunctor Q).map (left f g)).app X)
    (((strictDiagramFunctor Q).map (right f g)).app X) (bassGlue f g Q X)

/-- The comparison retains the original left inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:101"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent.", reassoc]
theorem comparison_left (X : C) :
    HomotopyPushout.inl (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫ comparison f g Q X =
      (((strictDiagramFunctor Q).map (left f g)).app X) :=
  HomotopyPushout.inl_desc _ _ _ _ _

/-- The comparison retains the original right inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:109"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent.", reassoc]
theorem comparison_right (X : C) :
    HomotopyPushout.inr (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫ comparison f g Q X =
      (((strictDiagramFunctor Q).map (right f g)).app X) :=
  HomotopyPushout.inr_desc _ _ _ _ _

/-- Every value of the original overlap is the Bass image of that same whole track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:116"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
theorem comparison_overlap (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F₀).obj X).space n) :
    (comparison f g Q X).map n
      (HomotopyPushout.cylinder (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) n (r, x)) =
      (strictDiagramMapHomotopy (glue f g) (glue_naturality f g) Q X).level n (r, x) := rfl

/-- The actual comparison commutes with every coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:124"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
theorem comparison_naturality {X Y : C} (k : X ⟶ Y) :
    (pushout ((strictDiagramFunctor Q).map f) ((strictDiagramFunctor Q).map g)).map k ≫
        comparison f g Q Y =
      comparison f g Q X ≫ ((strictDiagramFunctor Q).obj (pushout f g)).map k := by
  apply HomotopyPushout.hom_ext
  · apply Hom.ext
    funext n
    ext x
    change (((strictDiagramFunctor Q).map (left f g)).app Y).map n
      ((((strictDiagramFunctor Q).obj F₁).map k).map n x) =
      (((strictDiagramFunctor Q).obj (pushout f g)).map k).map n
        ((((strictDiagramFunctor Q).map (left f g)).app X).map n x)
    exact congrArg (fun a => a.map n x)
      (((strictDiagramFunctor Q).map (left f g)).naturality k)
  · apply Hom.ext
    funext n
    ext x
    change (((strictDiagramFunctor Q).map (right f g)).app Y).map n
      ((((strictDiagramFunctor Q).obj F₂).map k).map n x) =
      (((strictDiagramFunctor Q).obj (pushout f g)).map k).map n
        ((((strictDiagramFunctor Q).map (right f g)).app X).map n x)
    exact congrArg (fun a => a.map n x)
      (((strictDiagramFunctor Q).map (right f g)).naturality k)
  · intro n r x
    exact (strictDiagramMapHomotopy_naturality
      (glue f g) (glue_naturality f g) Q k n r x).symm

/-- The forward comparison is an actual natural transformation of spectrum diagrams. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutStrength.lean:152"
  "adaptation" "Original Bass action on the whole pushout overlap and forward descent."]
def rho : pushout ((strictDiagramFunctor Q).map f) ((strictDiagramFunctor Q).map g) ⟶
    (strictDiagramFunctor Q).obj (pushout f g) where
  app X := comparison f g Q X
  naturality _X _Y k := comparison_naturality f g Q k

end KTheory.Bass.PushoutStrength
