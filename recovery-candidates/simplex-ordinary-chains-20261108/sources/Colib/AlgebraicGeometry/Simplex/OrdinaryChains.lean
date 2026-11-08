/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Products
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Ordinary singular chains on the actual algebraic simplex

For an ordinary presheaf `P` on the existing smooth site over `Spec R`, the
simplicial presheaf in this file has value `P(U ×[Spec R] Δⁿ)` in degree `n`.
Its restrictions use the literal relative product maps. The associated complex
is Mathlib's `alternatingFaceMapComplex`, without a second chain-complex model.
Both the source restriction and the coefficient natural transformation retain
their original components. The coefficient category is any preadditive category,
with object and morphism universes independent of the base-ring universe.

This is the ordinary-presheaf part of MVW, Definition 2.14, generalized from
fields to commutative rings and from abelian groups to preadditive categories.
Transfers, sheafification and homotopy invariance are not asserted. The consumer
uses the existing native Dold-Kan normalization theorem rather than a new model.

Implementation adapted from `Motivic/Aglib/Algebra/Homology/SingularComplex/Presheaf.lean`
at revision a6805c4a87cdfd7717dd7a94039246a167f15380. Instead of migrating its
generic `SingularComplex` wrappers, we apply the native alternating-face functor.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A]

/-- The ordinary simplicial presheaf on the literal relative simplex products. -/
@[colib_ref "MVW2006" "Lecture 2, Definition 2.14, p. 16, ordinary-presheaf clause"
  "generalization" "Relative algebraic singular simplices over arbitrary commutative rings"]
def simplicialPresheaf (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) :
    SimplicialObject ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) where
  obj n :=
    { obj U := P.obj (op (SmoothSite.product U.unop ((cosimplicialSmoothSite R).obj n.unop)))
      map f := P.map (SmoothSite.productMap f.unop (𝟙 _)).op
      map_id U := by simp
      map_comp f g := by
        simp only [unop_comp, ← P.map_comp, ← op_comp, ← SmoothSite.productMap_comp,
          Category.id_comp] }
  map f :=
    { app U := P.map (SmoothSite.productMap (𝟙 U.unop)
        ((cosimplicialSmoothSite R).map f.unop)).op
      naturality U V g := by
        dsimp only
        simp only [← P.map_comp, ← op_comp, ← SmoothSite.productMap_comp,
          Category.id_comp, Category.comp_id] }
  map_id n := by
    ext U
    dsimp only
    simp
  map_comp f g := by
    ext U
    dsimp only
    simp only [NatTrans.comp_app, unop_comp, Functor.map_comp, ← P.map_comp, ← op_comp,
      ← SmoothSite.productMap_comp, Category.id_comp]

@[simp]
theorem simplicialPresheaf_obj_obj (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (n : ℕ) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    ((simplicialPresheaf R P).obj (op ⦋n⦌)).obj U =
      P.obj (op (SmoothSite.product U.unop (smoothSiteObj R n))) := rfl

@[simp]
theorem simplicialPresheaf_obj_map (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (n : ℕ) {U V : (SmoothSite (Spec (.of R)))ᵒᵖ} (f : U ⟶ V) :
    ((simplicialPresheaf R P).obj (op ⦋n⦌)).map f =
      P.map (SmoothSite.productMap f.unop (𝟙 (smoothSiteObj R n))).op := rfl

@[simp]
theorem simplicialPresheaf_δ_app (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    {n : ℕ} (i : Fin (n + 2)) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    ((simplicialPresheaf R P).δ i).app U =
      P.map (SmoothSite.productMap (𝟙 U.unop) ((cosimplicialSmoothSite R).δ i)).op := rfl

/-- Natural transformations of the original presheaves act componentwise on simplices. -/
def simplicialPresheafFunctor :
    ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ⥤
      SimplicialObject ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) where
  obj := simplicialPresheaf R
  map α :=
    { app n :=
        { app U := α.app (op (SmoothSite.product U.unop ((cosimplicialSmoothSite R).obj n.unop)))
          naturality U V f := α.naturality (SmoothSite.productMap f.unop (𝟙 _)).op }
      naturality n m f := by
        ext U
        exact α.naturality (SmoothSite.productMap (𝟙 U.unop)
          ((cosimplicialSmoothSite R).map f.unop)).op }
  map_id P := rfl
  map_comp α β := rfl

variable [Preadditive A]

/-- The actual ordinary singular chains, using the native alternating-face complex. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/SingularComplex/Presheaf.lean:35-47,85-95"
  "adaptation" "Ordinary relative singular chains via native alternatingFaceMapComplex",
  colib_ref "MVW2006" "Lecture 2, Definition 2.14, p. 16, alternating-chain clause"
    "generalization" "Ordinary presheaf singular chains over any commutative base ring"]
def singularChainsFunctor : ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ⥤
    ChainComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ℕ :=
  simplicialPresheafFunctor R ⋙ alternatingFaceMapComplex _

@[simp]
theorem singularChainsFunctor_obj_X_obj (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (n : ℕ) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).obj P).X n).obj U =
      P.obj (op (SmoothSite.product U.unop (smoothSiteObj R n))) := rfl

/-- The differential keeps the ordered barycentric faces and their integer signs. -/
theorem singularChainsFunctor_obj_d_app (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (n : ℕ) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).obj P).d (n + 1) n).app U =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (SmoothSite.productMap (𝟙 U.unop) ((cosimplicialSmoothSite R).δ i)).op := by
  change (((alternatingFaceMapComplex _).obj (simplicialPresheaf R P)).d
    (n + 1) n).app U = _
  simp [AlternatingFaceMapComplex.objD]
  rfl

/-- In degree one the differential is face zero minus face one. -/
theorem singularChainsFunctor_obj_d_one_zero_app
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).obj P).d 1 0).app U =
      P.map (SmoothSite.productMap (𝟙 U.unop)
        ((cosimplicialSmoothSite R).δ (0 : Fin 2))).op -
      P.map (SmoothSite.productMap (𝟙 U.unop)
        ((cosimplicialSmoothSite R).δ (1 : Fin 2))).op := by
  rw [singularChainsFunctor_obj_d_app]
  simp [Fin.sum_univ_two, sub_eq_add_neg]
  rfl

@[simp]
theorem singularChainsFunctor_map_f_app {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A}
    (α : P ⟶ Q) (n : ℕ) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).map α).f n).app U =
      α.app (op (SmoothSite.product U.unop (smoothSiteObj R n))) := rfl

instance : (simplicialPresheafFunctor R (A := A)).Additive where
  map_add := rfl

instance : (singularChainsFunctor R (A := A)).Additive := inferInstanceAs
  (simplicialPresheafFunctor R ⋙ alternatingFaceMapComplex _).Additive

end AlgebraicSimplex
