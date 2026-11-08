/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRowNaturality


/-! # Original transformation components on the canonical one-step quotient row

Strict chosen-zero equalities identify the full original row transformation with the
original one-row embedding of its component. Endpoint transports are retained explicitly.
-/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/SConstruction/Rows/OneRowTransformation.lean`
   at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
   Original objects, maps, hypotheses and universe parameters are retained.
   Source-only preparation; native validation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v u' v'
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (η : F ⟶ G) (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF hF0 hG0 in
/-- The actual transformation on a canonical row keeps its original component and zero maps. -/
theorem oneDiagram_transformation_app (A : C) (p : Interval ⦋1⦌) :
    HEq (η.app ((oneDiagram V A).obj p))
      (((oneEmbedding W).map (η.app A)).hom.app p) := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  fin_cases a <;> fin_cases b
  all_goals first
    | rfl
    | apply (conj_eqToHom_iff_heq _ _ hF0 hG0).mp
      exact (hF.zero V.isZero).eq_of_src _ _

end CategoryTheory.Waldhausen.QuotientRows
