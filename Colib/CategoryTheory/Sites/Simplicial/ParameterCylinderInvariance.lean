/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderDerived
public import Colib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

import Colib.CategoryTheory.Sites.Hypercohomology.KInjectiveEvaluation
import Colib.CategoryTheory.Sites.Hypercohomology.ParameterEvaluation
import Colib.CategoryTheory.Sites.Hypercohomology.Shift
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# From representable restrictions to pointed cylinder invariance

Invertibility on ordinary hypercohomology along every representable
projection makes the corresponding map of underlying K-injective
presheaf complexes a pointwise quasi-isomorphism. The parameter
coproduct comparison gives invariance for every pointed cylinder.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe d t v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v t}]
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max u v t})]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_sections_homologyMap_of_hypercohomology
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ) [I.IsKInjective] (n : ℤ)
    {X Y : C} (f : X ⟶ Y)
    (h : IsIso ((hypercohomologyPresheaf.{d, max u t} J I n).map f.op)) :
    IsIso (HomologicalComplex.homologyMap
      ((((sheafSections J AddCommGrpCat.{max u v t}).map f.op).mapHomologicalComplex
        (.up ℤ)).app I) n) := by
  let eX := kInjectiveEvaluationAddEquiv.{d, t} J X I n
  let eY := kInjectiveEvaluationAddEquiv.{d, t} J Y I n
  let r := HomologicalComplex.homologyMap
    ((((sheafSections J AddCommGrpCat.{max u v t}).map f.op).mapHomologicalComplex
      (.up ℤ)).app I) n
  let R := (hypercohomologyPresheaf.{d, max u t} J I n).map f.op
  have hcomm : eX ∘ r = R ∘ eY := funext fun x ↦
    kInjectiveEvaluationAddEquiv_naturality.{d, t} J f I n x
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective r
  rw [← Function.Bijective.of_comp_iff' eX.bijective r, hcomm]
  exact ((ConcreteCategory.isIso_iff_bijective _).mp h).comp eY.bijective

variable [HasBinaryProducts C]
  [IsGrothendieckAbelian.{max u v t} (Sheaf J AddCommGrpCat.{max u v t})] (V : C)

set_option backward.isDefEq.respectTransparency false in
/-- Affine projection invariance on smooth representables in every degree
suffices for reduced hypercohomology invariance on every pointed cylinder. -/
theorem bijective_reducedHypercohomology_map_cylinder
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ)
    (h : ∀ (n : ℤ) (U : C), IsIso ((hypercohomologyPresheaf.{d, max u t} J K n).map
      (prod.fst : U ⨯ V ⟶ U).op))
    (p : ℤ) (X : PointedSimplicialPresheaf.{max u v t} C) :
    Function.Bijective ((reducedHypercohomology C J K p).map
      (cylinderProjection X (liftedRepresentableInterval V)).op) := by
  let A := Sheaf J AddCommGrpCat.{max u v t}
  let R := Stacks.Injectives.kInjectiveResolutionFunctor A
  let I := R.obj K
  let L := I⟦p⟧
  have : I.IsKInjective := inferInstanceAs ((R.obj K).IsKInjective)
  have : L.IsKInjective := inferInstanceAs ((I⟦p⟧).IsKInjective)
  let Q : _ ⥤ DerivedCategory.{d} A := DerivedCategory.Q
  let i := (Stacks.Injectives.kInjectiveResolutionInclusion A).app K
  have : IsIso (Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).mpr
      (Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso A K)
  let a : Q.obj K ≅ Q.obj I := asIso (Q.map i)
  let e : Q.obj L ≅ (Q.obj K)⟦p⟧ :=
    (Q.commShiftIso p).app I ≪≫ (shiftFunctor _ p).mapIso a.symm
  have hL (n : ℤ) (U : C) :
      IsIso ((hypercohomologyPresheaf.{d, max u t} J L n).map
        (prod.fst : U ⨯ V ⟶ U).op) := by
    let f : U ⨯ V ⟶ U := prod.fst
    let F := derivedHomPresheafFunctor.{d, max u t} J (p + n)
    have hI : IsIso ((F.obj (Q.obj I)).map f.op) :=
      (NatIso.isIso_map_iff (F.mapIso a) f.op).mp (h (p + n) U)
    exact (NatIso.isIso_map_iff (hypercohomologyShiftPresheafIso J I p n) f.op).mpr hI
  have hπ := ParameterCoproduct.quasiIso_homologicalProjectionPullback_of_isIso_sections_homologyMap
    J V AddCommGrpCat.{max u v t} (.up ℤ) L (fun U n ↦
      isIso_sections_homologyMap_of_hypercohomology C J L n (prod.fst : U ⨯ V ⟶ U) (hL n U))
  exact bijective_reducedHypercohomology_map_cylinder_of_kInjective C J K p L e V hπ X

end CategoryTheory.PointedSimplicialPresheaf
