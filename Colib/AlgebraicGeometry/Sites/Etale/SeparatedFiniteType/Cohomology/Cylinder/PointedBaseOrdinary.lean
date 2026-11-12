/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.PointLocallyZero
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.FiberComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PointColimit
public import Colib.CategoryTheory.Sites.Cohomology.LocalTriviality

/-! # Positive original ordinary cohomology has zero actual base-neighborhood germs -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/PointedBaseOrdinary.lean`, blob
`e72d3cc3ee3fba0a0ded39ad19a3bc1df7bb02e5`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]

/-- The original big-site base-neighborhood diagram is the actual small-site point diagram. -/
def pointedBaseOrdinaryIso (n : ℕ) :
    pointedBaseValues R Φ
      (cohomologyPresheaf.{u + 1, u + 1} F n) ≅
      (Functor.Elements.π Φ.fiber).op ⋙
        cohomologyPresheaf.{u + 1, u + 1} ((restrict X AddCommGrpCat).obj F) n :=
  NatIso.ofComponents (fun V =>
    (cohomologyRestrictionEquiv X F n V.unop.obj).toAddCommGrpIso) (by
    intro V W f
    ext x
    exact cohomologyRestrictionEquiv_restriction F n
      ((Functor.Elements.π Φ.fiber).map f.unop) x)

/-- Positive base germs vanish by actual ordinary local effacement and the actual point axiom. -/
theorem pointedBaseColimit_isZero_succ (n : ℕ) :
    IsZero (colimit (pointedBaseValues R Φ
      (cohomologyPresheaf.{u + 1, u + 1} F (n + 1)))) := by
  have h := Φ.presheafFiber_isZero_of_locally_zero
    (cohomologyPresheaf.{u + 1, u + 1} ((restrict X AddCommGrpCat).obj F) (n + 1))
    (fun V s => zeroSieve_mem_succ (nisnevichTopology X.left)
      ((restrict X AddCommGrpCat).obj F) n V s)
  exact h.of_iso (colim.mapIso (pointedBaseOrdinaryIso R X Φ F (n + 1)))

/-- For positive original cohomology, only the punctured projection comparison is needed
for vanishing of the actual cylinder restriction; base-germ vanishing is supplied. -/
theorem pointedCylinderRestriction_colimit_eq_zero_succ
    {U : SmoothSite (Spec R)} (j : U ⟶ X) (n : ℕ)
    [IsIso (colim.map (pointedProjection R Φ
      (cohomologyPresheaf.{u + 1, u + 1} F (n + 1)) (pointedPuncture R j Φ)))] :
    colim.map (pointedCylinderRestriction R j Φ
      (cohomologyPresheaf.{u + 1, u + 1} F (n + 1))) = 0 :=
  pointedCylinderRestriction_colimit_eq_zero R j Φ _
    (pointedBaseColimit_isZero_succ R X Φ F n)

/-- The actual positive higher-direct-image point fiber vanishes once the punctured
comparison and the original cylinder-restriction monomorphism have been proved. -/
theorem pointedProjectionFiber_isZero_succ
    [HasExt.{u + 1}
      (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
        AddCommGrpCat.{u + 1})]
    {U : SmoothSite (Spec R)} (j : U ⟶ X) (n : ℕ)
    [IsIso (colim.map (pointedProjection R Φ
      (cohomologyPresheaf.{u + 1, u + 1} F (n + 1)) (pointedPuncture R j Φ)))]
    [Mono (colim.map (pointedCylinderRestriction R j Φ
      (cohomologyPresheaf.{u + 1, u + 1} F (n + 1))))] :
    IsZero (Φ.sheafFiber.obj
      (((directImage
        ((SmoothSite.Contraction.projection
          (SmoothSite.additiveGroupObject (Spec R))).app X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X)
          AddCommGrpCat.{u + 1}).obj F))) :=
  (pointedCylinder_colimit_isZero R j Φ _
    (pointedBaseColimit_isZero_succ R X Φ F n)).of_iso
      (pointedCylinderColimitFiberIso R X Φ F (n + 1)).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
