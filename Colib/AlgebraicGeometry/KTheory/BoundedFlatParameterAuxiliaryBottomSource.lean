/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliarySupportNull
public import Colib.CategoryTheory.Functor.FullSubcategoryExt

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryBottomSource.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original bottom-auxiliary source map is the literal open-set cast

For the inclusion of an actual open, the union with the bottom auxiliary open is
that same open. The original `toBasic` map equals transport through this precise
open-set equality. Equality is detected after the actual full-subcategory
inclusion on each parameter Model, before any K-theory functor is applied.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport

private theorem supported_eqToHom_forget {Q : Scheme.{u}} {U V : Q.Opens} (h : U = V) :
    eqToHom (congrArg (fun W : Q.Opens => ParameterModels.supported W.ι) h) ≫
      ParameterModels.forget V.ι = ParameterModels.forget U.ι := by
  subst V
  simp

/-- The union with the bottom auxiliary open is the original open itself. -/
theorem unionOpen_ι_bot {Q : Scheme.{u}} (U : Q.Opens) : unionOpen U.ι ⊥ = U := by
  simp [unionOpen]

/-- The original source comparison is exactly transport by the displayed open-set equality. -/
theorem toBasic_ι_bot_eqToHom {Q : Scheme.{u}} (U : Q.Opens)
    (h : unionOpen U.ι ⊥ = U := unionOpen_ι_bot U) :
    toBasic U.ι ⊥ =
      eqToHom (congrArg (fun V : Q.Opens => ParameterModels.supported V.ι) h) := by
  apply NatTrans.ext
  funext X
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  apply CategoryTheory.Functor.ext_of_comp_fullSubcategory
  exact congrArg (fun k ↦ k.hom.toFunctor) (NatTrans.congr_app
    ((toBasic_forget U.ι ⊥).trans (supported_eqToHom_forget h).symm) X)

/-- The actual bottom-auxiliary source map is an isomorphism of the original Model diagrams. -/
instance toBasic_ι_bot_isIso {Q : Scheme.{u}} (U : Q.Opens) : IsIso (toBasic U.ι ⊥) := by
  rw [toBasic_ι_bot_eqToHom U]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
