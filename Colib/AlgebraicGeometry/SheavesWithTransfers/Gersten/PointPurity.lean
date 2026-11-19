/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.PointPurity.Stage
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.PointPurity.Generic
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Nisnevich support cohomology at a point -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open Opposite TopologicalSpace AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.MotivicHomotopy Stacks.Cohomology.FreeYonedaUnivLE

universe u w w' w'' v v'

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

private def colimitAddEquivOfStagewise {I : Type u} [Category I]
    (P : Iᵒᵖ ⥤ AddCommGrpCat.{v}) (Q : Iᵒᵖ ⥤ AddCommGrpCat.{v'})
    [HasColimit P] [HasColimit Q]
    (e : ∀ x : I, P.obj (op x) ≃+ Q.obj (op x))
    (he : ∀ {x y : I} (f : x ⟶ y) (a : P.obj (op y)),
      e x (P.map f.op a) = Q.map f.op (e y a)) :
    (colimit P : AddCommGrpCat.{v}) ≃+ (colimit Q : AddCommGrpCat.{v'}) := by
  let L := AddCommGrpCat.uliftFunctor.{v', v}
  let R := AddCommGrpCat.uliftFunctor.{v, v'}
  let E : P ⋙ L ≅ Q ⋙ R :=
    NatIso.ofComponents (fun j =>
      ((AddEquiv.ulift.trans (e j.unop)).trans AddEquiv.ulift.symm).toAddCommGrpIso) (by
      intro a b f
      apply ConcreteCategory.hom_ext
      intro z
      exact congrArg ULift.up (he f.unop z.down))
  let H := preservesColimitIso L P ≪≫ HasColimit.isoOfNatIso E ≪≫
    (preservesColimitIso R Q).symm
  exact AddEquiv.ulift.symm.trans (H.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] effectiveSupportCoefficientCorSheafify
  effectiveSupportCoefficientSmoothSheafify

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]

local notation "K" => effectiveHICoefficient k

variable (X : SmoothSite (Spec (CommRingCat.of k))) (x : X.left)
  (F : LargeSheaves k) (hF : F.obj.IsA1Invariant)

section Model

variable {U₀ : PointSupportNeighborhoods k X x}
  (h₀ : Smooth ((pointClosureInclusion k X x ∣_ U₀.1) ≫
    (Scheme.Opens.ι (X := X.left) U₀.1 ≫ X.hom)))
  {a b : ℕ} (hX : RelativeDimension ((opensFunctor X).obj U₀.1).hom a)
  (hZ : RelativeDimension (smoothPointClosure h₀).hom b)

local notation "I" => Set.Iic U₀
local notation "Z₀" => smoothPointClosure h₀
local notation "η" => smoothPointCenterGeneric h₀
set_option quotPrecheck false in
local notation "G" => (toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1

include hX hZ

set_option maxHeartbeats 1000000 in
-- Form the stage comparisons before moving to the opposite category in the abstract colimit.
private def pointSupportModelCohomologyColimitEquiv (n : ℕ) (hn : a - b ≤ n) :
    (colimit (pointSupportSubneighborhoodInclusion k X x U₀ ⋙
      pointSupportCohomologyDiagram k X (K F hF) (n : ℤ) x) : AddCommGrpCat.{w'}) ≃+
    (colimit ((smoothPointCenterFunctor h₀).op ⋙
      cohomologyPresheaf.{u + 1, u + 1} (G) (n - (a - b))) : AddCommGrpCat.{u + 1}) := by
  let P : Iᵒᵖ ⥤ AddCommGrpCat.{w'} := pointSupportSubneighborhoodInclusion k X x U₀ ⋙
    pointSupportCohomologyDiagram k X (K F hF) (n : ℤ) x
  let Q : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1} := (smoothPointCenterFunctor h₀).op ⋙
    cohomologyPresheaf.{u + 1, u + 1} (G) (n - (a - b))
  let e (U : I) : P.obj (op U) ≃+ Q.obj (op U) :=
    subneighborhoodSupportCohomologyEquiv h₀ hX hZ F hF U n hn
  have he {U V : I} (r : U ⟶ V) (z : P.obj (op V)) :
      e U (P.map r.op z) = Q.map r.op (e V z) :=
    subneighborhoodSupportCohomologyEquiv_naturality h₀ hX hZ F hF r n hn z
  exact colimitAddEquivOfStagewise P Q e he

set_option maxHeartbeats 1000000 in
-- Use both cofinal neighborhood inclusions and the actual centre comparisons.
/-- Above or at the codimension, supported cohomology at the point is the
ordinary cohomology germ of the contracted sheaf on the smooth reduced closure. -/
@[no_expose]
def pointSupportCohomologyGermEquivOfModel (n : ℕ) (hn : a - b ≤ n) :
    pointSupportCohomology k X (K F hF) (n : ℤ) x ≃+
      (colimit (smoothCohomologyGermDiagram (Z₀) (η) (G) (n - (a - b))) :
        AddCommGrpCat.{u + 1}) := by
  let m := n - (a - b)
  let H := cohomologyPresheaf.{u + 1, u + 1} (G) m
  let P : Iᵒᵖ ⥤ AddCommGrpCat.{w'} := pointSupportSubneighborhoodInclusion k X x U₀ ⋙
    pointSupportCohomologyDiagram k X (K F hF) (n : ℤ) x
  let Q : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1} := (smoothPointCenterFunctor h₀).op ⋙ H
  let e : pointSupportCohomology k X (K F hF) (n : ℤ) x ≅ colimit P :=
    (pointSupportSubneighborhoodColimitIso k X (K F hF) (n : ℤ) x U₀).symm
  let e' : (colimit P : AddCommGrpCat.{w'}) ≃+ (colimit Q : AddCommGrpCat.{u + 1}) :=
    pointSupportModelCohomologyColimitEquiv k X x F hF h₀ hX hZ n hn
  let q := smoothPointCenterNeighborhoods h₀
  let j := (OpenNhds.inclusion (η) ⋙ opensFunctor (Z₀)).op
  let D := smoothCohomologyGermDiagram (Z₀) (η) (G) m
  let e'' : Q ≅ q.op ⋙ D :=
    Functor.isoWhiskerRight (NatIso.op (smoothPointCenterFunctorIso h₀)).symm H ≪≫
      Functor.associator q.op j H
  let e''' : colimit Q ≅ colimit D :=
    HasColimit.isoOfNatIso e'' ≪≫ Functor.Final.colimitIso q.op D
  exact e.addCommGroupIsoToAddEquiv.trans (e'.trans e'''.addCommGroupIsoToAddEquiv)

set_option maxHeartbeats 400000 in
-- Transport the ordinary germ in its native category before taking the additive equivalence.
/-- The degree equal to the codimension is the germ of the contracted sheaf
on the smooth model of the residue field. -/
def pointSupportPurityEquivOfModel :
    pointSupportCohomology k X (K F hF) ((a - b : ℕ) : ℤ) x ≃+
      smoothSectionGerm (Z₀) (η) (G) := by
  let p := a - b
  let T (m : ℕ) : AddCommGrpCat.{u + 1} :=
    colimit (smoothCohomologyGermDiagram (Z₀) (η) (G) m)
  let e : pointSupportCohomology k X (K F hF) (p : ℤ) x ≃+ T (p - p) :=
    pointSupportCohomologyGermEquivOfModel k X x F hF h₀ hX hZ p le_rfl
  let e₀ : T (p - p) ≅ T 0 := eqToIso (congrArg T (Nat.sub_self p))
  let g : T 0 ≅ smoothSectionGerm (Z₀) (η) (G) :=
    smoothCohomologyGermZeroIso (Z₀) (η) (G)
  exact e.trans ((e₀ ≪≫ g).addCommGroupIsoToAddEquiv)

private theorem subsingleton_pointSupportCohomology_of_lt (n : ℤ) (hn : n < (a - b : ℕ)) :
    Subsingleton (pointSupportCohomology k X (K F hF) n x) := by
  let P := pointSupportSubneighborhoodInclusion k X x U₀ ⋙
    pointSupportCohomologyDiagram k X (K F hF) n x
  let e := (pointSupportSubneighborhoodColimitIso k X (K F hF) n x U₀).symm
  have hι (U : (Set.Iic U₀)ᵒᵖ) : colimit.ι P U = 0 := by
    apply ConcreteCategory.hom_ext
    intro c
    have hc : c = 0 := subneighborhoodSupport_eq_zero_of_lt h₀ hX hZ F hF U.unop n hn c
    let f := (colimit.ι P U).hom
    change f c = 0
    exact (congrArg f hc).trans f.map_zero'
  have hz : 𝟙 (colimit P) = 0 := by
    apply colimit.hom_ext
    intro U
    rw [Category.comp_id, comp_zero, hι U]
  let : Subsingleton (colimit P : AddCommGrpCat.{w'}) :=
    AddCommGrpCat.isZero_iff_subsingleton.1 ((IsZero.iff_id_eq_zero _).2 hz)
  exact e.addCommGroupIsoToAddEquiv.injective.subsingleton

private theorem subsingleton_pointSupportCohomology_of_gt (n : ℕ) (hn : a - b < n) :
    Subsingleton (pointSupportCohomology k X (K F hF) (n : ℤ) x) := by
  let : Nonempty (pointClosureOpen k X x U₀.1).toScheme :=
    pointClosureOpen_nonempty U₀.1 U₀.2
  let : IsIntegral (Z₀).left :=
    inferInstanceAs (IsIntegral (pointClosureOpen k X x U₀.1).toScheme)
  have hη : IsGenericPoint (η) Set.univ := isGenericPoint_pointClosureGeneric U₀.1 U₀.2
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (show n - (a - b) ≠ 0 by omega)
  let e := pointSupportCohomologyGermEquivOfModel k X x F hF h₀ hX hZ n (Nat.le_of_lt hn)
  have hz : Subsingleton (colimit (smoothCohomologyGermDiagram (Z₀) (η) (G) (n - (a - b))) :
      AddCommGrpCat.{u + 1}) :=
    hr.symm ▸ subsingleton_smoothCohomologyGerm_succ (Z₀) (η) (G) hη r
  let := hz
  exact e.injective.subsingleton

end Model

set_option maxHeartbeats 700000 in
-- Shrink to an actual smooth reduced closure and compare its dimension drop.
/-- The Nisnevich support group at a point of codimension `p` vanishes in all
other degrees, including at nonclosed points of the smooth scheme. -/
theorem subsingleton_pointSupportCohomology_of_ne {p : ℕ} (hp : Order.coheight x = p)
    (n : ℤ) (hn : n ≠ (p : ℤ)) :
    Subsingleton (pointSupportCohomology k X (K F hF) n x) := by
  obtain ⟨U, hxU, _, h₀, a, b, hX, hZ, hcod⟩ :=
    exists_pure_smooth_pointClosure_restriction k X x ⊤ (by trivial)
  have hc : a - b = p := by exact_mod_cast hcod.symm.trans hp
  let U₀ : PointSupportNeighborhoods k X x := ⟨U, hxU⟩
  rcases lt_or_gt_of_ne hn with hlo | hhi
  · exact subsingleton_pointSupportCohomology_of_lt k X x F hF (U₀ := U₀)
      h₀ hX hZ n (by simpa only [hc] using hlo)
  · have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    rw [← hcast]
    exact subsingleton_pointSupportCohomology_of_gt k X x F hF (U₀ := U₀)
      h₀ hX hZ n.toNat (by omega)

/-- The support object at a point is zero in degrees other than its codimension. -/
@[colib_tag "COL-1309", colib_ref "Voevodsky2000CohomologicalTransfers" "Lemma 4.36"
  "adaptation" "Concentration of the represented point support groups in the codimension"]
theorem isZero_pointSupportCohomology_of_ne {p : ℕ} (hp : Order.coheight x = p)
    (n : ℤ) (hn : n ≠ (p : ℤ)) :
    IsZero (pointSupportCohomology k X (K F hF) n x) :=
  AddCommGrpCat.isZero_iff_subsingleton.2
    (subsingleton_pointSupportCohomology_of_ne k X x F hF hp n hn)

set_option maxHeartbeats 700000 in
-- Use the smooth model's dimension proofs after identifying its codimension.
/-- The degree-`p` support group is identified with the germ of `F_{-p}`
on a smooth model of the residue field of the point. -/
@[colib_tag "COL-1309", colib_ref "Voevodsky2000CohomologicalTransfers" "Lemma 4.36"
  "adaptation" "The degree-matching group and the contraction germ on a smooth model"]
theorem exists_pointSupportPurityEquiv {p : ℕ} (hp : Order.coheight x = p) :
    ∃ (U : PointSupportNeighborhoods k X x)
      (hU : Smooth ((pointClosureInclusion k X x ∣_ U.1) ≫
        (Scheme.Opens.ι (X := X.left) U.1 ≫ X.hom))),
      Nonempty (pointSupportCohomology k X (K F hF) (p : ℤ) x ≃+
        smoothSectionGerm (smoothPointClosure hU) (smoothPointCenterGeneric hU)
          ((toSheaf k).obj (iteratedHIContraction k p F hF).1)) := by
  obtain ⟨U, hxU, _, hU, a, b, hX, hZ, hcod⟩ :=
    exists_pure_smooth_pointClosure_restriction k X x ⊤ (by trivial)
  have hc : p = a - b := by exact_mod_cast hp.symm.trans hcod
  let U₀ : PointSupportNeighborhoods k X x := ⟨U, hxU⟩
  let e := pointSupportPurityEquivOfModel k X x F hF (U₀ := U₀) hU hX hZ
  subst p
  exact ⟨U₀, hU, ⟨e⟩⟩

end AlgebraicGeometry.SheafWithTransfers.Gersten
