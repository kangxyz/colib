/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.ClosedImmersion
public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.Coefficients.Contraction
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Purity on supported Hom with homotopy invariant transfer coefficients -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

/-- The canonical additive sheafification on the Nisnevich correspondence site. -/
local instance effectiveSupportCoefficientCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The canonical additive sheafification on the smooth Nisnevich site. -/
local instance effectiveSupportCoefficientSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "NST" => LargeSheaves k
local notation "M" => effectiveSmoothMotive k
local notation "K" => effectiveHICoefficient k
local notation "L" => effectiveLefschetzTwistFunctor k

/-- The abelian structure on the original transfer coefficients. -/
local instance effectiveSupportCoefficientAbelian : Abelian NST := SheafWithTransfers.abelian k

variable {Z X : SmoothSite (Spec (.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left] {a b : ℕ}
  (hX : RelativeDimension X.hom a) (hZ : RelativeDimension Z.hom b)

/-- The actual purity isomorphism identifies supported Hom with contracted coefficients. -/
def effectiveSupportCohomologyEquiv (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) :
    (effectiveMotiveWithSupport k i ⟶ (K F hF)⟦n⟧) ≃+
      ((M).obj Z ⟶ (K (iteratedHIContraction k (a - b) F hF).1
        (iteratedHIContraction k (a - b) F hF).2)⟦n - ((a - b : ℕ) : ℤ)⟧) :=
  (AddEquiv.mk' (effectivePurity k i hX hZ).homFromEquiv
    (fun x y => Preadditive.comp_add _ _ _ (effectivePurity k i hX hZ).inv x y)).trans
      (effectiveLefschetzPowerCohomologyEquiv k ((M).obj Z) (a - b) F hF n)

set_option maxHeartbeats 600000 in
-- Transport precomposition through the two actual iterated Lefschetz targets.
/-- A commuting square of purity comparisons gives the restriction on supported Hom. -/
theorem effectiveSupportCohomologyEquiv_precomp {Z' X' : SmoothSite (Spec (.of k))} (j : Z' ⟶ X')
    [IsClosedImmersion j.left] (hX' : RelativeDimension X'.hom a) (hZ' : RelativeDimension Z'.hom b)
    {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
    (hp : effectiveMotiveWithSupportMap k h ≫ (effectivePurity k j hX' hZ').hom =
      (effectivePurity k i hX hZ).hom ≫ (Stabilization.iterate L (a - b)).map ((M).map g))
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ)
    (x : effectiveMotiveWithSupport k j ⟶ (K F hF)⟦n⟧) :
    effectiveSupportCohomologyEquiv k i hX hZ F hF n
        (effectiveMotiveWithSupportMap k h ≫ x) =
      (M).map g ≫ effectiveSupportCohomologyEquiv k j hX' hZ' F hF n x := by
  let e := effectivePurity k i hX hZ
  let e' := effectivePurity k j hX' hZ'
  let l := Stabilization.iterate L (a - b)
  have h' : e.inv ≫ effectiveMotiveWithSupportMap k h = l.map ((M).map g) ≫ e'.inv := by
    apply (cancel_mono e'.hom).mp
    change _ = (l.map ((M).map g) ≫ e'.inv) ≫ e'.hom
    rw [Category.assoc, hp, e.inv_hom_id_assoc, Category.assoc, e'.inv_hom_id, Category.comp_id]
  let q := effectiveMotiveWithSupportMap k h
  let gM := (M).map g
  let z := e'.inv ≫ x
  let E := effectiveLefschetzPowerCohomologyEquiv k ((M).obj Z) (a - b) F hF n
  have h₀ := (Category.assoc e.inv q x).symm
  have h₁ := congrArg (· ≫ x) h'
  have h₂ := Category.assoc (l.map gM) e'.inv x
  have hLift := congrArg (fun t => E t) (h₀.trans (h₁.trans h₂))
  have hNat := effectiveLefschetzPowerCohomologyEquiv_precomp k gM (a - b) F hF n z
  have hFinal := hLift.trans hNat
  exact hFinal

end AlgebraicGeometry.MotivicHomotopy
