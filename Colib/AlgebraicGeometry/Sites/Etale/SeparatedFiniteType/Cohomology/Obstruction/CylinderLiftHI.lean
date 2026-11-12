/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Obstruction.LiftHI
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChangeNaturality

/-!
# Lifting first obstructions on the original cylinder

The affine-line base-change isomorphism transports a local lift to the
literal cylinder projection on the refined étale test object.

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Obstruction/CylinderLiftHI.lean`, blob
`63aecbe025a9f436dbde029bda6b624c2a04f250`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})]

local notation "cylinder" => (SmoothSite.Contraction.affineLineCylinder.obj X)
set_option quotPrecheck false in
local notation "projection" =>
  ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X)

/-- The obstruction is evaluated on the literal original neighborhood cylinder. -/
def a1TestObstruction (N : ℕ) (V : EtaleSeparatedFiniteType X.left)
    (α : (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N).obj
      (Opposite.op (SmoothSite.Contraction.affineLineCylinder.obj ((toSmoothSite X).obj V)))) :
    (((directImage (projection).left).rightDerived N).obj
      ((restrict cylinder AddCommGrpCat.{u + 1}).obj
        ((toSheaf k).obj F))).obj.obj (Opposite.op V) :=
  originalFirstObstruction (projection)
      ((toSheaf k).obj F) N V
    ((cohomologyPresheaf.{u + 1, u + 1}
      ((toSheaf k).obj F) N).map (a1BaseChangeIso (.of k) X
          V).hom.op α)

/-- After shrinking, the lift is along the literal projection of the actual cylinder. -/
theorem a1_exists_open_projection_lift
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (V : EtaleSeparatedFiniteType X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (α : (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N).obj
      (Opposite.op (SmoothSite.Contraction.affineLineCylinder.obj ((toSmoothSite X).obj V))))
    (hα : ∀ y : V.left, g y ⤳ z →
      markedSectionGerm
        (((directImage (projection).left).rightDerived N).obj
          ((restrict cylinder
              AddCommGrpCat.{u + 1}).obj
            ((toSheaf k).obj F))).obj V y (a1TestObstruction X F N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      A1.projectionPullback (.of k)
        (cohomologyPresheaf.{u + 1, u + 1}
          ((toSheaf k).obj F) N) ((toSmoothSite X).obj
              (testOpenObject V (g ⁻¹ᵁ O))) β =
      (cohomologyPresheaf.{u + 1, u + 1}
        ((toSheaf k).obj F) N).map
          (SmoothSite.Contraction.affineLineCylinder.map ((toSmoothSite X).map
            (testOpenInclusion V (g ⁻¹ᵁ O)))).op α := by
  let P := cohomologyPresheaf.{u + 1, u + 1}
    ((toSheaf k).obj F) N
  obtain ⟨O, hz, β, hβ⟩ := a1_exists_open_originalRestriction_lift X F hF N hN hLow V g z
    (P.map (a1BaseChangeIso (.of k) X V).hom.op α) hα
  refine ⟨O, hz, β, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (P.map (a1BaseChangeIso (.of k) X
        (testOpenObject V (g ⁻¹ᵁ O))).hom.op)).1
  change P.map _ (P.map _ β) = P.map _ (P.map _ α)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    a1BaseChangeIso_hom_projection]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← a1BaseChangeIso_naturality, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  exact hβ

end AlgebraicGeometry.SheafWithTransfers
