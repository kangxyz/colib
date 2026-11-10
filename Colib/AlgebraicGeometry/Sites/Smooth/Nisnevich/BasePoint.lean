/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Evaluation
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# The base-field point of the smooth Nisnevich site

Pulling back a covering sieve along a base-field point gives the maximal
sieve at the base. The constant one-object diagram at the base therefore
defines a point, whose presheaf and sheaf fibers are the actual evaluations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Scheme.SmoothSite

open GrothendieckTopology.Point

local instance : HasInitial (Discrete PUnit.{1}) :=
  (IsInitial.ofUniqueHom (X := (⟨PUnit.unit⟩ : Discrete PUnit.{1}))
    (fun Y => eqToHom (Subsingleton.elim _ Y))
    (fun _ _ => Subsingleton.elim _ _)).hasInitial

variable (k : Type u) [Field k]

/-- The constant one-object diagram at the actual base of the smooth site. -/
abbrev nisnevichBasePointDiagram :
    Discrete PUnit.{1} ⥤ SmoothSite (Spec (.of k)) :=
  Functor.fromPUnit.{0} (base (Spec (.of k)))

/-- A covering sieve contains every morphism from the actual base scheme. -/
theorem mem_nisnevich_covering_sieve_of_base_map {X : SmoothSite (Spec (.of k))}
    {R : Sieve X} (hR : R ∈ nisnevichTopology (Spec (.of k)) X)
    (f : base (Spec (.of k)) ⟶ X) : R f :=
  (R.mem_iff_pullback_eq_top f).mpr
    (nisnevich_covering_sieve_base_eq_top k
      ((nisnevichTopology (Spec (.of k))).pullback_stable f hR))

/-- The one-object diagram lifts covers using the given map from the base. -/
theorem nisnevichBasePointCoverLift ⦃X : SmoothSite (Spec (.of k))⦄ (R : Sieve X)
    (hR : R ∈ nisnevichTopology (Spec (.of k)) X) ⦃U : Discrete PUnit.{1}⦄
    (f : (nisnevichBasePointDiagram k).obj U ⟶ X) :
    ∃ (Y : SmoothSite (Spec (.of k))) (g : Y ⟶ X) (_ : R g) (V : Discrete PUnit.{1})
      (q : V ⟶ U) (a : (nisnevichBasePointDiagram k).obj V ⟶ Y),
      a ≫ g = (nisnevichBasePointDiagram k).map q ≫ f :=
  ⟨base (Spec (.of k)), f, mem_nisnevich_covering_sieve_of_base_map k hR f,
    U, 𝟙 U, 𝟙 _, rfl⟩

/-- The actual base-field point of the smooth Nisnevich site. -/
def nisnevichBasePoint : GrothendieckTopology.Point.{u} (nisnevichTopology (Spec (.of k))) :=
  ofIsCofiltered.{u} (nisnevichBasePointDiagram k) (nisnevichBasePointCoverLift k)

/-- The germ in the base-field point represented by the identity on the base. -/
def nisnevichBasePointIdGerm : (nisnevichBasePoint k).fiber.obj (base (Spec (.of k))) :=
  ofIsCofiltered.fiberMk.{u} (p := nisnevichBasePointDiagram k) (U := ⊥_ _) (𝟙 _)

variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u} A]

/-- Presheaf fiber at the base-field point is evaluation at the actual base scheme. -/
def nisnevichBasePointPresheafFiberIso :
    (nisnevichBasePoint k).presheafFiber (A := A) ≅
      (CategoryTheory.evaluation (SmoothSite (Spec (.of k)))ᵒᵖ A).obj
        (op (base (Spec (.of k)))) := by
  let η := (nisnevichBasePoint k).toPresheafFiberNatTrans (A := A) _
    (nisnevichBasePointIdGerm k)
  letI : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    change IsIso ((presheafFiberOfIsCofilteredCocone.{u}
      (nisnevichBasePointDiagram k) (nisnevichBasePointCoverLift k) P).ι.app (op (⊥_ _)))
    exact (isColimitPresheafFiberOfIsCofilteredCocone.{u}
      (nisnevichBasePointDiagram k) (nisnevichBasePointCoverLift k) P).isIso_ι_app_of_isTerminal
      _ initialIsInitial.op
  exact (asIso η).symm

@[simp]
theorem nisnevichBasePointPresheafFiberIso_inv_app (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ A) :
    (nisnevichBasePointPresheafFiberIso k A).inv.app P =
      (nisnevichBasePoint k).toPresheafFiber _ (nisnevichBasePointIdGerm k) P :=
  rfl

/-- Sheaf fiber at the base-field point is the native sections functor at the base. -/
def nisnevichBasePointSheafFiberIso :
    (nisnevichBasePoint k).sheafFiber (A := A) ≅
      (sheafSections (nisnevichTopology (Spec (.of k))) A).obj (op (base (Spec (.of k)))) :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ A) (nisnevichBasePointPresheafFiberIso k A)

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_tag "COL-0392"]
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichBasePoint
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichBasePointPresheafFiberIso
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichBasePointSheafFiberIso

attribute [colib_ref "MVW2006"
  "Lecture 12, Example 12.2, p. 89" "ingredient"
  "Cover splitting at the field spectrum gives the evaluation point diagram"]
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichBasePoint
