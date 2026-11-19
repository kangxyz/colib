/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.Coefficients.EffectiveSupport
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Nisnevich purity for homotopy invariant transfer coefficients

The complementary open computes ordinary cohomology with support. Motivic
purity and the reduced torus adjunction give the corresponding iterated
Laurent contraction on the smooth closed centre.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme Opposite Stacks.Cohomology.FreeYonedaUnivLE
open SmoothSite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local notation "Nis" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))

/-- Use the canonical sheafification on the correspondence site. -/
local instance ordinarySupportCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The ordinary purity comparison uses the canonical additive sheafification. -/
local instance supportHasSheafify : HasSheafify Nis AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} Nis

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "NST" => LargeSheaves k
local notation "M" => effectiveSmoothMotive k
local notation "K" => effectiveHICoefficient k
local notation "L" => effectiveLefschetzTwistFunctor k

variable {Z X : SmoothSite (Spec (.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left] {a b : ℕ}
  (hX : RelativeDimension X.hom a) (hZ : RelativeDimension Z.hom b)

private def supportDegreeIso (F : NST) (hF : F.obj.IsA1Invariant) (c n : ℕ) (hn : c ≤ n) :
    (K F hF)⟦(n : ℤ) - (c : ℤ)⟧ ≅ (K F hF)⟦((n - c : ℕ) : ℤ)⟧ :=
  eqToIso (congrArg (fun r : ℤ => (K F hF)⟦r⟧) (Int.ofNat_sub hn).symm)

/-- Purity for ordinary Nisnevich cohomology with smooth closed support. -/
@[no_expose]
def supportCohomologyPurityEquiv (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) (hn : a - b ≤ n) :
    relativeH.{u + 1, u + 1} Nis (closedPairOpenInclusion i.left) ((toSheaf k).obj F) n ≃+
      (cohomologyPresheaf.{u + 1, u + 1}
        ((toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1) (n - (a - b))).obj (op Z) := by
  let C := iteratedHIContraction k (a - b) F hF
  let e := supportDegreeIso k C.1 C.2 (a - b) n hn
  exact (effectivePairCohomologyEquiv k (closedPairOpenInclusion i.left) F hF n).symm.trans
    ((effectiveSupportCohomologyEquiv k i hX hZ F hF (n : ℤ)).trans
      ((AddEquiv.mk' e.homToEquiv (fun x y => Preadditive.add_comp _ _ _ x y e.hom)).trans
        (effectiveSmoothCohomologyEquiv k Z C.1 C.2 (n - (a - b)))))

include hX hZ in
/-- Ordinary Nisnevich cohomology with smooth closed support vanishes below the codimension. -/
theorem supportCohomology_eq_zero_of_lt (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (hn : n < a - b)
    (x : relativeH.{u + 1, u + 1} Nis (closedPairOpenInclusion i.left) ((toSheaf k).obj F) n) :
    x = 0 := by
  let C := iteratedHIContraction k (a - b) F hF
  let e := (effectivePairCohomologyEquiv k (closedPairOpenInclusion i.left) F hF n).symm.trans
    (effectiveSupportCohomologyEquiv k i hX hZ F hF (n : ℤ))
  let y := e x
  have hn' : (n : ℤ) - ((a - b : ℕ) : ℤ) < 0 := by omega
  have hZero := effectiveSmoothCohomology_eq_zero_of_neg k Z C.1 C.2
    ((n : ℤ) - ((a - b : ℕ) : ℤ)) hn' y
  have h := hZero.trans e.map_zero.symm
  exact e.injective h

private def supportCohomologyClassOfMotive (F : NST) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (hn : a - b ≤ n) (x : effectiveMotiveWithSupport k i ⟶ (K F hF)⟦(n : ℤ)⟧) :
    (cohomologyPresheaf.{u + 1, u + 1}
      ((toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1) (n - (a - b))).obj (op Z) :=
  let C := iteratedHIContraction k (a - b) F hF
  let d := supportDegreeIso k C.1 C.2 (a - b) n hn
  effectiveSmoothCohomologyEquiv k Z C.1 C.2 (n - (a - b))
    (effectiveSupportCohomologyEquiv k i hX hZ F hF (n : ℤ) x ≫ d.hom)

private theorem supportCohomologyPurityEquiv_apply (F : NST) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (hn : a - b ≤ n)
    (x : relativeH.{u + 1, u + 1} Nis (closedPairOpenInclusion i.left) ((toSheaf k).obj F) n) :
    supportCohomologyPurityEquiv k i hX hZ F hF n hn x =
      supportCohomologyClassOfMotive k i hX hZ F hF n hn
        ((effectivePairCohomologyEquiv k (closedPairOpenInclusion i.left) F hF n).symm x) :=
  rfl

set_option maxHeartbeats 850000 in
-- Compose the original purity square with the common shift and smooth graph comparison.
private theorem supportCohomologyClassOfMotive_precomp {Z' X' : SmoothSite (Spec (.of k))}
    (j : Z' ⟶ X') [IsClosedImmersion j.left]
    (hX' : RelativeDimension X'.hom a) (hZ' : RelativeDimension Z'.hom b)
    {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
    (hp : effectiveMotiveWithSupportMap k h ≫ (effectivePurity k j hX' hZ').hom =
      (effectivePurity k i hX hZ).hom ≫ (Stabilization.iterate L (a - b)).map ((M).map g))
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) (hn : a - b ≤ n)
    (x : effectiveMotiveWithSupport k j ⟶ (K F hF)⟦(n : ℤ)⟧) :
    supportCohomologyClassOfMotive k i hX hZ F hF n hn
        (effectiveMotiveWithSupportMap k h ≫ x) =
      (cohomologyPresheaf.{u + 1, u + 1}
          ((toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1) (n - (a - b))).map g.op
        (supportCohomologyClassOfMotive k j hX' hZ' F hF n hn x) := by
  let C := iteratedHIContraction k (a - b) F hF
  let d := supportDegreeIso k C.1 C.2 (a - b) n hn
  let t := effectiveSupportCohomologyEquiv k j hX' hZ' F hF (n : ℤ) x
  let H := effectiveSmoothCohomologyEquiv k Z C.1 C.2 (n - (a - b))
  have hRaw := effectiveSupportCohomologyEquiv_precomp k i hX hZ j hX' hZ' h hp F hF n x
  have h₁ := congrArg (fun v => H (v ≫ d.hom)) hRaw
  have h₂ := congrArg (fun v => H v) (Category.assoc ((M).map g) t d.hom)
  have h₃ := effectiveSmoothCohomologyEquiv_precomp k g C.1 C.2 (n - (a - b)) (t ≫ d.hom)
  have hFinal := h₁.trans (h₂.trans h₃)
  exact hFinal

set_option maxHeartbeats 650000 in
-- Cancel the pair comparison and its inverse on a given supported motive class.
private theorem supportCohomologyPurityEquiv_of_motive (F : NST) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (hn : a - b ≤ n) (x : effectiveMotiveWithSupport k i ⟶ (K F hF)⟦(n : ℤ)⟧) :
    supportCohomologyPurityEquiv k i hX hZ F hF n hn
        (effectivePairCohomologyEquiv k (closedPairOpenInclusion i.left) F hF n x) =
      supportCohomologyClassOfMotive k i hX hZ F hF n hn x := by
  let A := effectivePairCohomologyEquiv k (closedPairOpenInclusion i.left) F hF n
  let P := supportCohomologyClassOfMotive k i hX hZ F hF n hn
  have hx := A.symm_apply_apply x
  have hStart := supportCohomologyPurityEquiv_apply k i hX hZ F hF n hn (A x)
  have hEnd := congrArg P hx
  exact hStart.trans hEnd

attribute [local irreducible] supportCohomologyPurityEquiv supportCohomologyClassOfMotive

set_option backward.isDefEq.respectTransparency true in
set_option Elab.async false in
set_option maxHeartbeats 1200000 in
-- Realize the forward pair action on the source side before the centre comparison.
private theorem supportCohomologyPurityEquiv_restricted_motive
    {Z' X' : SmoothSite (Spec (.of k))} (j : Z' ⟶ X') [IsClosedImmersion j.left]
    {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) (hn : a - b ≤ n)
    (x : effectiveMotiveWithSupport k j ⟶ (K F hF)⟦(n : ℤ)⟧) :
    supportCohomologyPurityEquiv k i hX hZ F hF n hn
        (((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map
          (closedSupportArrowMap h).op
            (effectivePairCohomologyEquiv k (closedPairOpenInclusion j.left) F hF n x)) =
      supportCohomologyClassOfMotive k i hX hZ F hF n hn
        (effectiveMotiveWithSupportMap k h ≫ x) := by
  let P := supportCohomologyPurityEquiv k i hX hZ F hF n hn
  let pairMap := closedSupportArrowMap (i := i) (j := j) (f := f) (g := g) h
  let q := (effectivePairMotiveFunctor k).map pairMap
  have hPair := effectivePairCohomologyEquiv_precomp k (closedPairOpenInclusion i.left)
    (j' := closedPairOpenInclusion j.left) pairMap F hF n x
  have hStart := congrArg P.toFun hPair.symm
  have hImage := supportCohomologyPurityEquiv_of_motive k i hX hZ F hF n hn (q ≫ x)
  have hRestriction := hStart.trans hImage
  -- Pass the inferred equality to the kernel at the stated relative-cohomology type.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `hRestriction
      | throwError "Missing the inferred restriction comparison"
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar decl.fvarId)

set_option Elab.async false in
set_option maxHeartbeats 1200000 in
-- Transport restriction on the image of the original pair comparison.
private theorem supportCohomologyPurityEquiv_precomp_motive_image
    {Z' X' : SmoothSite (Spec (.of k))} (j : Z' ⟶ X') [IsClosedImmersion j.left]
    (hX' : RelativeDimension X'.hom a) (hZ' : RelativeDimension Z'.hom b)
    {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
    (hp : effectiveMotiveWithSupportMap k h ≫ (effectivePurity k j hX' hZ').hom =
      (effectivePurity k i hX hZ).hom ≫ (Stabilization.iterate L (a - b)).map ((M).map g))
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) (hn : a - b ≤ n)
    (x : effectiveMotiveWithSupport k j ⟶ (K F hF)⟦(n : ℤ)⟧) :
    supportCohomologyPurityEquiv k i hX hZ F hF n hn
        (((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map
          (closedSupportArrowMap h).op
            (effectivePairCohomologyEquiv k (closedPairOpenInclusion j.left) F hF n x)) =
      (cohomologyPresheaf.{u + 1, u + 1}
          ((toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1) (n - (a - b))).map g.op
        (supportCohomologyPurityEquiv k j hX' hZ' F hF n hn
          (effectivePairCohomologyEquiv k (closedPairOpenInclusion j.left) F hF n x)) := by
  let C := iteratedHIContraction k (a - b) F hF
  let s := (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj C.1) (n - (a - b))).map g.op
  have hLeft := supportCohomologyPurityEquiv_restricted_motive k i hX hZ j h F hF n hn x
  have hNat := supportCohomologyClassOfMotive_precomp k i hX hZ j hX' hZ' h hp F hF n hn x
  have hRight := supportCohomologyPurityEquiv_of_motive k j hX' hZ' F hF n hn x
  have hEnd := congrArg (fun t => s t) hRight.symm
  have hFinal := hLeft.trans (hNat.trans hEnd)
  exact hFinal

set_option maxHeartbeats 950000 in
-- Match the maps on the ordinary relative groups using the surjective pair comparison.
/-- A commuting purity square gives the same ordinary restriction on the contracted centre. -/
theorem supportCohomologyPurityEquiv_precomp {Z' X' : SmoothSite (Spec (.of k))} (j : Z' ⟶ X')
    [IsClosedImmersion j.left] (hX' : RelativeDimension X'.hom a) (hZ' : RelativeDimension Z'.hom b)
    {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
    (hp : effectiveMotiveWithSupportMap k h ≫ (effectivePurity k j hX' hZ').hom =
      (effectivePurity k i hX hZ).hom ≫ (Stabilization.iterate L (a - b)).map ((M).map g))
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) (hn : a - b ≤ n)
    (x : relativeH.{u + 1, u + 1} Nis (closedPairOpenInclusion j.left) ((toSheaf k).obj F) n) :
    supportCohomologyPurityEquiv k i hX hZ F hF n hn
        (((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map
          (closedSupportArrowMap h).op x) =
      (cohomologyPresheaf.{u + 1, u + 1}
          ((toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1) (n - (a - b))).map g.op
        (supportCohomologyPurityEquiv k j hX' hZ' F hF n hn x) := by
  let C := iteratedHIContraction k (a - b) F hF
  let B := effectivePairCohomologyEquiv k (closedPairOpenInclusion j.left) F hF n
  let r := ((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map
    (closedSupportArrowMap h).op
  let s := (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj C.1) (n - (a - b))).map g.op
  let P := fun t => supportCohomologyPurityEquiv k i hX hZ F hF n hn (r t)
  let Q := fun t => s (supportCohomologyPurityEquiv k j hX' hZ' F hF n hn t)
  have hImage := supportCohomologyPurityEquiv_precomp_motive_image k i hX hZ j hX' hZ' h
    hp F hF n hn
  have hComp : P ∘ (fun t => B t) = Q ∘ (fun t => B t) := funext hImage
  have hEq := B.surjective.injective_comp_right hComp
  exact congrFun hEq x

end AlgebraicGeometry.MotivicHomotopy
