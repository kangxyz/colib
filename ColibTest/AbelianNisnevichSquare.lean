/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.AbelianSquareDescent
import Colib.CategoryTheory.Sites.FreeYonedaPushout
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Abelian descent on geometric Nisnevich squares

The square is an actual pullback of smooth-site objects. Its open arrow and
etale arrow satisfy the closed-complement isomorphism condition. The existing
geometric descent theorem proves both section-gluing hypotheses and the
pushout of native free representing sheaves. No sheaf pullback or free-sheaf
pushout is assumed as an input.

The final example directly uses Mathlib's existing free-abelian pushout theorem
for its native Mayer-Vietoris square. It is not copied into production.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u v

section SmoothSquare

variable {S : Scheme.{u}} (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

example : (sq.map (freeYoneda.{u + 1} (nisnevichTopology S))).IsPushout :=
  isPushout_map_freeYoneda (nisnevichTopology S) sq
    (fun F ↦ isPullback_op_map_of_iso_complement sq hpb z hcomp F)

example (E : ShortComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}))
    (hE : E.ShortExact)
    (hsurj : Function.Surjective (fun a :
        E.X₁.obj.obj (op sq.X₂) × E.X₁.obj.obj (op sq.X₃) =>
      E.X₁.obj.map sq.f₁₂.op a.1 - E.X₁.obj.map sq.f₁₃.op a.2))
    (s : E.X₃.obj.obj (op sq.X₄))
    (lA : E.X₂.obj.obj (op sq.X₂)) (lY : E.X₂.obj.obj (op sq.X₃))
    (hA : E.g.hom.app (op sq.X₂) lA = E.X₃.obj.map sq.f₂₄.op s)
    (hY : E.g.hom.app (op sq.X₃) lY = E.X₃.obj.map sq.f₃₄.op s) :
    ∃ l : E.X₂.obj.obj (op sq.X₄), E.g.hom.app (op sq.X₄) l = s := by
  have h₂ : (sq.op.map (E.X₂.obj ⋙ forget AddCommGrpCat.{u + 1})).IsPullback :=
    isPullback_op_map_of_iso_complement sq hpb z hcomp
      ((sheafCompose (nisnevichTopology S) (forget AddCommGrpCat.{u + 1})).obj E.X₂)
  have h₃ : (sq.op.map (E.X₃.obj ⋙ forget AddCommGrpCat.{u + 1})).IsPullback :=
    isPullback_op_map_of_iso_complement sq hpb z hcomp
      ((sheafCompose (nisnevichTopology S) (forget AddCommGrpCat.{u + 1})).obj E.X₃)
  exact Sheaf.exists_section_lift_of_square_difference_surjective
    (nisnevichTopology S) hE sq h₂ h₃ hsurj s lA lY hA hY

example (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (g : (freeYoneda.{u + 1} (nisnevichTopology S)).obj sq.X₄ ⟶ F) :
    sectionsEquiv sq.X₂ F
        ((freeYoneda.{u + 1} (nisnevichTopology S)).map sq.f₂₄ ≫ g) =
      F.obj.map sq.f₂₄.op (sectionsEquiv sq.X₄ F g) :=
  sectionsEquiv_naturality_left sq.f₂₄ F g

end SmoothSquare

section NativeMayerVietoris

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrpCat.{v}]

example (sq : J.MayerVietorisSquare) :
    (sq.toSquare.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J _)).IsPushout :=
  sq.isPushoutAddCommGrpFreeSheaf

end NativeMayerVietoris
