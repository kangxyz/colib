/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitComplex
public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains

/-!
# The actual sheafified singular units complex

The current ordinary singular construction already uses literal products.
Consequently the raw term comparison is the identity, not the old categorical
product adapter. Only the native sheafification counit is needed after the
all-degree differential comparison. This is the actual-map adaptation of
UnitSheafification.lean at motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicTopology Opposite AlgebraicSimplex
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- The literal sheaf differential retains every geometric face and its integer sign. -/
theorem unitUnderlying_d_app (n : ℕ) (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    (((sheafToPresheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
      ((unitSingularSheafComplex k).d (n + 1) n)).app X) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (largeUnitsPresheaf (Spec (.of k))).map
        (productMap (𝟙 X.unop) ((cosimplicialSmoothSite k).δ i)).op := by
  have h := AlternatingFaceMapComplex.obj_d_eq (unitSimplicialSheaf k) n
  have he := congrArg (fun f =>
    ((sheafToPresheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).map f).app X) h
  simp only [Functor.map_sum, Functor.map_zsmul, NatTrans.app_sum, NatTrans.app_zsmul] at he
  exact he

/-- The raw complexes use the very same literal products, with identity components. -/
def unitRawComplexIso :
    (singularChainsFunctor k).obj (largeUnitsPresheaf (Spec (.of k))) ≅
      ((sheafToPresheaf (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).obj
        (unitSingularSheafComplex k) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst i
    apply NatTrans.ext
    funext X
    change 𝟙 _ ≫
        (((sheafToPresheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
          ((unitSingularSheafComplex k).d (j + 1) j)).app X) =
      (((singularChainsFunctor k).obj (largeUnitsPresheaf (Spec (.of k)))).d
        (j + 1) j).app X ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, unitUnderlying_d_app,
      singularChainsFunctor_obj_d_app])

@[simp] theorem unitRawComplexIso_hom_f (n : ℕ) :
    (unitRawComplexIso k).hom.f n = 𝟙 _ := rfl

/-- Sheafification followed by the actual counit gives the units sheaf complex. -/
def unitSheafifiedSingularIso :
    (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
        (largeUnitsPresheaf (Spec (.of k))) ≅ unitSingularSheafComplex k :=
  ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
    AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).mapIso (unitRawComplexIso k) ≪≫
      (NatIso.mapHomologicalComplex
        (asIso (sheafificationAdjunction (nisnevichTopology (Spec (.of k)))
          AddCommGrpCat.{u + 1}).counit) (.down ℕ)).app (unitSingularSheafComplex k)

end AlgebraicGeometry.Scheme.SmoothSite
