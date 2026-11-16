/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.ModelDoubleLaurentQuotient
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionSwap

/-!
# Original connective double-cone permutation from the actual quotient sign

The same original double-Laurent inclusion descends through the four actual
chart relations. Its proved epimorphism transfers the independently defined
quotient swap sign to the actual geometric double-cone permutation. The input
is a sign on the original fixed quotient, never a conjugate definition of it.

Adapted from the original construction in
`Quillen/KTheory/Bass/ModelDoubleLaurentSign.lean`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open KTheory.Bass.TwoChart
universe u w
namespace KTheory.Bass.GeometricConeInterchange
local notation "p" => NatTrans.op PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op PolynomialLaurent.Relative.minus

/-- The unchanged stable degree-zero row on the actual quasi-compact parameter schemes. -/
def quasiCompactStableZero (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  quasiCompactSchemesInclusion.op ⋙ F ⋙ stableHomotopyFunctor 0

/-- Descent of the original double-Laurent inclusion through its four actual relations. -/
def doubleLaurentQuotientMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contraction p m (contraction p m (quasiCompactStableZero F))).obj X ⟶
      (stableHomotopyFunctor 0).obj
        ((coneFunctor.obj (coneFunctor.obj F)).obj (op X.unop.obj)) :=
  doubleContractionDesc p m (quasiCompactStableZero F) X
    ((stableHomotopyFunctor 0).map (doubleLaurentInclusion F (op X.unop.obj)))
    (doubleLaurentInclusion_zero_inner_plus F hF (op X.unop.obj))
    (doubleLaurentInclusion_zero_inner_minus F hF (op X.unop.obj))
    (doubleLaurentInclusion_zero_outer_plus F hF (op X.unop.obj))
    (doubleLaurentInclusion_zero_outer_minus F hF (op X.unop.obj))

/-- The two original quotient projections recover the unchanged whole inclusion. -/
@[reassoc]
theorem doubleLaurentQuotientMap_π (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleContractionπ p m (quasiCompactStableZero F) X ≫
        doubleLaurentQuotientMap F hF X =
      (stableHomotopyFunctor 0).map (doubleLaurentInclusion F (op X.unop.obj)) :=
  doubleContractionπ_desc _ _ _ _ _ _ _ _ _

private theorem quotient_sign {A B C : AddCommGrpCat.{w}}
    (j : A ⟶ C) (q : A ⟶ B) (d : B ⟶ C) (s : A ⟶ A)
    (t : B ⟶ B) (r : C ⟶ C) [Epi j]
    (hd : q ≫ d = j) (hs : q ≫ t = s ≫ q) (ht : t = -𝟙 B)
    (hr : j ≫ r = s ≫ j) : r = -𝟙 C := by
  apply (cancel_epi j).1
  rw [hr, ← hd, ← Category.assoc, ← hs, ht]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id]

/-- The independently proved original quotient sign determines the actual cone permutation. -/
theorem permutation_zero_neg_of_quotient_swap
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w}) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (M ⋙ prespectrumFunctor)) X = -𝟙 _) :
    (stableHomotopyFunctor 0).map
      (permutation (M ⋙ prespectrumFunctor) (op X.unop.obj)).hom = -𝟙 _ := by
  let F := M ⋙ prespectrumFunctor
  have hF : ∀ Y, LinearZeroGrowth (F.obj Y) := fun Y => model_linearZeroGrowth (M.obj Y)
  let G := quasiCompactStableZero F
  let L := PolynomialLaurent.Relative.laurentFunctor.op
  let A := G.obj (L.obj (L.obj X))
  let B := (contraction p m (contraction p m G)).obj X
  let C := (stableHomotopyFunctor 0).obj
    ((coneFunctor.obj (coneFunctor.obj F)).obj (op X.unop.obj))
  let j : A ⟶ C :=
    (stableHomotopyFunctor 0).map (doubleLaurentInclusion F (op X.unop.obj))
  let q : A ⟶ B := doubleContractionπ p m G X
  let d : B ⟶ C := doubleLaurentQuotientMap F hF X
  let s : A ⟶ A := G.map (PolynomialLaurent.Relative.doubleLaurentOppositeSwap.hom.app X)
  let t : B ⟶ B := PolynomialLaurent.Relative.doubleContractionSwap G X
  let r : C ⟶ C := (stableHomotopyFunctor 0).map (permutation F (op X.unop.obj)).hom
  have : Epi j := doubleLaurentInclusion_zero_epi M (op X.unop.obj)
  have hd : q ≫ d = j := doubleLaurentQuotientMap_π F hF X
  have hs : q ≫ t = s ≫ q := PolynomialLaurent.Relative.doubleContractionπ_swap G X
  have ht : t = -𝟙 B := h
  have hr : j ≫ r = s ≫ j :=
    doubleLaurentInclusion_permutation_stable F (op X.unop.obj) 0
  exact quotient_sign j q d s t r hd hs ht hr

end KTheory.Bass.GeometricConeInterchange
