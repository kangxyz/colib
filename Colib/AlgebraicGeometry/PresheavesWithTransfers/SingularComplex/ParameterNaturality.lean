/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor.ParameterNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterSwap

/-!
# Naturality of the singular parameter permutation in the parameter

The degreewise permutations exchange the actual simplex and parameter
factors. Their compatibility with a parameter morphism uses the graph of
the original product, including the structural projection and unit section.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k] (T V : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral V.hom]
  {W : SmoothSite (Spec (.of k))} [GeometricallyIntegral W.hom]

/-- The same permutation is natural for morphisms of its second parameter. -/
@[reassoc]
theorem parameterProductSwapNatIso_secondParameterMap (f : V ⟶ W) (X : Cor k) :
    (parameterProductMap f).app ((parameterProduct T).obj X) ≫
        (parameterProductSwapNatIso T W).hom.app X =
      (parameterProductSwapNatIso T V).hom.app X ≫
        (parameterProduct T).map ((parameterProductMap f).app X) := by
  simp only [parameterProductMap_app, parameterProductSwapNatIso_hom_app,
    parameterProduct_graph, ← Functor.map_comp]
  apply (graphFunctor k).congr_map
  have h := SmoothSite.productSwapLast_naturality X.toSmoothSite T V (𝟙 _) (𝟙 T) f
  rwa [SmoothSite.productMap_id] at h

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {V W : SmoothSite (Spec (.of k))} [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom]

private theorem signed_parameter_square_at
    (f : V ⟶ W) (n : ℕ) (X : Cor k) :
    let T := AlgebraicSimplex.smoothSiteObj k n
    let E := Cor.parameterProduct T
    let F := Cor.parameterProduct V
    let F' := Cor.parameterProduct W
    let a : E.obj (F.obj X) ⟶ E.obj (F'.obj X) := E.map ((Cor.parameterProductMap f).app X)
    let b : F.obj (E.obj X) ⟶ F'.obj (E.obj X) := (Cor.parameterProductMap f).app (E.obj X)
    let e : F.obj (E.obj X) ⟶ E.obj (F.obj X) :=
      (Cor.parameterProductSwapNatIso T V).hom.app X
    let e' : F'.obj (E.obj X) ⟶ E.obj (F'.obj X) :=
      (Cor.parameterProductSwapNatIso T W).hom.app X
    transfer P a ≫ transfer P e = transfer P e' ≫ transfer P b := by
  let T := AlgebraicSimplex.smoothSiteObj k n
  let E := Cor.parameterProduct T
  let F := Cor.parameterProduct V
  let F' := Cor.parameterProduct W
  let a : E.obj (F.obj X) ⟶ E.obj (F'.obj X) := E.map ((Cor.parameterProductMap f).app X)
  let b : F.obj (E.obj X) ⟶ F'.obj (E.obj X) := (Cor.parameterProductMap f).app (E.obj X)
  let e : F.obj (E.obj X) ⟶ E.obj (F.obj X) :=
    (Cor.parameterProductSwapNatIso T V).hom.app X
  let e' : F'.obj (E.obj X) ⟶ E.obj (F'.obj X) :=
    (Cor.parameterProductSwapNatIso T W).hom.app X
  change transfer P a ≫ transfer P e = transfer P e' ≫ transfer P b
  exact (transfer_comp P e a).symm.trans <| (congrArg (transfer P)
    (Cor.parameterProductSwapNatIso_secondParameterMap T V f X).symm).trans
      (transfer_comp P b e')

/-- The signed parameter permutation commutes with the original pullback
of the second parameter in every singular chain degree. -/
theorem withParameterSingularComplexIso_hom_parameterMap (f : V ⟶ W) :
    ((withParameterPullbackNatTrans f).mapHomologicalComplex (.down ℕ)).app
        (singularComplex P) ≫ (withParameterSingularComplexIso P V).hom =
      (withParameterSingularComplexIso P W).hom ≫ singularComplexMap (parameterPullback P f) := by
  apply HomologicalComplex.hom_f_injective
  funext n
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  exact signed_parameter_square_at P f n U.unop

/-- The inverse permutation satisfies the corresponding original chain square. -/
theorem withParameterSingularComplexIso_inv_parameterMap (f : V ⟶ W) :
    singularComplexMap (parameterPullback P f) ≫ (withParameterSingularComplexIso P V).inv =
      (withParameterSingularComplexIso P W).inv ≫
        ((withParameterPullbackNatTrans f).mapHomologicalComplex (.down ℕ)).app
          (singularComplex P) := by
  let e := withParameterSingularComplexIso P V
  let e' := withParameterSingularComplexIso P W
  let r := singularComplexMap (parameterPullback P f)
  let t := ((withParameterPullbackNatTrans f).mapHomologicalComplex (.down ℕ)).app
    (singularComplex P)
  change r ≫ e.inv = e'.inv ≫ t
  apply (cancel_mono e.hom).1
  have h : t ≫ e.hom = e'.hom ≫ r :=
    withParameterSingularComplexIso_hom_parameterMap P f
  calc
    _ = r := (Category.assoc _ _ _).trans
      ((congrArg (r ≫ ·) e.inv_hom_id).trans (Category.comp_id r))
    _ = e'.inv ≫ e'.hom ≫ r := (e'.inv_hom_id_assoc r).symm
    _ = _ := (congrArg (e'.inv ≫ ·) h.symm).trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.PresheafWithTransfers
