/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterSwap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf

/-!
# The singular complex and parameter reindexing

The signed permutation identifies each degree on the actual product
schemes and commutes with every algebraic coface. The alternating
differential therefore retains its original signs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  (V : SmoothSite (Spec (.of k))) [GeometricallyIntegral V.hom]

local notation "T" => withParameterFunctor V
local notation "Δ(" n ")" => _root_.AlgebraicSimplex.smoothSiteObj k n

/-- The literal factor permutation on each signed singular term. -/
def withParameterSingularTermIso (n : ℕ) :
    (T).obj ((singularComplex P).X n) ≅ (singularComplex (withParameter P V)).X n :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight
    (NatIso.op (Cor.parameterProductSwapNatIso (Δ(n)) V)) P.obj)

@[simp]
theorem withParameterSingularTermIso_hom_app (n : ℕ) (X : Cor k) :
    (withParameterSingularTermIso P V n).hom.hom.app (op X) =
      transfer P ((Cor.parameterProductSwapNatIso (Δ(n)) V).hom.app X) :=
  rfl

/-- The original parameter reindexing commutes with the original signed
singular complex by the graphs of the degreewise permutations. -/
def withParameterSingularComplexIso :
    ((T).mapHomologicalComplex (.down ℕ)).obj (singularComplex P) ≅
      singularComplex (withParameter P V) :=
  HomologicalComplex.Hom.isoOfComponents (withParameterSingularTermIso P V) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst i
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    change transfer P ((Cor.parameterProductSwapNatIso (Δ(j + 1)) V).hom.app X.unop) ≫
        ((singularComplex (withParameter P V)).d (j + 1) j).hom.app X =
      ((singularComplex P).d (j + 1) j).hom.app
        (op ((Cor.parameterProduct V).obj X.unop)) ≫
        transfer P ((Cor.parameterProductSwapNatIso (Δ(j)) V).hom.app X.unop)
    rw [singularComplex_d_app (withParameter P V) j X.unop,
      singularComplex_d_app P j ((Cor.parameterProduct V).obj X.unop)]
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro index _
    apply congrArg ((-1 : ℤ) ^ (index : ℕ) • ·)
    let δ : Δ(j) ⟶ Δ(j + 1) :=
      (_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ index
    let f := (Cor.parameterProductMap δ).app X.unop
    let g := (Cor.parameterProductMap δ).app ((Cor.parameterProduct V).obj X.unop)
    change transfer P ((Cor.parameterProductSwapNatIso (Δ(j + 1)) V).hom.app X.unop) ≫
        transfer P ((Cor.parameterProduct V).map f) =
      transfer P g ≫ transfer P ((Cor.parameterProductSwapNatIso (Δ(j)) V).hom.app X.unop)
    rw [← transfer_comp, ← transfer_comp]
    exact congrArg (transfer P) (Cor.parameterProductSwapNatIso_parameterMap (Δ(j)) V δ X.unop))

end AlgebraicGeometry.PresheafWithTransfers
