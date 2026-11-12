/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Limits.FiniteSubfieldBaseChange
import Colib.AlgebraicGeometry.Sites.Smooth.Basic

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry IntermediateField

universe u

noncomputable section

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]

example : IsColimit (finsetAdjoinCocone K L) := finsetAdjoinIsColimit K L

example : IsColimit (finsetAdjoinAlgebraCocone K L) := finsetAdjoinAlgebraIsColimit K L

example (s : Finset L) : Module.Finite K (adjoin K (s : Set L)) :=
  finite_finsetAdjoinDiagram_obj K L s

example (s : Finset L) : Algebra.IsSeparable K (adjoin K (s : Set L)) :=
  isSeparable_finsetAdjoinDiagram_obj K L s

example : IsLimit (finsetSubfieldSpecCone K L) := finsetSubfieldSpecConeIsLimit K L

example {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    (finsetSubfieldBaseChangeCone K L f).pt =
      pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))) f := rfl

example {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    IsLimit (finsetSubfieldBaseChangeCone K L f) := finsetSubfieldBaseChangeConeIsLimit K L f

example {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) {s t : (Finset L)ᵒᵖ} (g : s ⟶ t) :
    IsAffineHom ((finsetSubfieldBaseChangeDiagram K L f).map g) := inferInstance

example {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of K)) (s : (Finset L)ᵒᵖ) :
    CompactSpace ((finsetSubfieldBaseChangeDiagram K L f).obj s) ∧
      QuasiSeparatedSpace ((finsetSubfieldBaseChangeDiagram K L f).obj s) :=
  ⟨inferInstance, inferInstance⟩

/-- The statement has no Infinite K assumption, including for the actual separable closure. -/
example (s : Finset (SeparableClosure K)) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (adjoin K (s : Set (SeparableClosure K)))))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap K (adjoin K (s : Set (SeparableClosure K)))))) :=
  ⟨isFinite_finsetSubfieldSpec K (SeparableClosure K) s,
    etale_finsetSubfieldSpec K (SeparableClosure K) s⟩

/-- A model over a finite separable field remains an object over the original coefficient field.
No presheaf on the extension field or correspondence-field-change functor is used. -/
example (k : Type u) [Field k] (X : Scheme.SmoothSite (Spec (.of k)))
    (f : X.left ⟶ Spec (.of K)) (s : Finset L) :
    Scheme.smoothSeparatedFiniteType
      (pullback.snd (Spec.map (CommRingCat.ofHom
        (algebraMap K (adjoin K (s : Set L))))) f ≫ X.hom) := by
  have := isFinite_finsetSubfieldSpec K L s
  have := etale_finsetSubfieldSpec K L s
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- The original marking equation survives every actual finite-stage projection. -/
example {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (s : Finset L)
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ (finsetSubfieldBaseChangeCone K L f).pt) :
    (ξ ≫ (finsetSubfieldBaseChangeCone K L f).π.app (op s)) ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K (adjoin K (s : Set L))))) f =
      ξ ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L))) f := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q ↦ ξ ≫ q) (finsetSubfieldBaseChangeCone_π_snd K L f s))

#print axioms finsetAdjoinIsColimit
#print axioms finsetAdjoinAlgebraIsColimit
#print axioms finsetSubfieldBaseChangeConeIsLimit
#print axioms etale_finsetSubfieldSpec

end
