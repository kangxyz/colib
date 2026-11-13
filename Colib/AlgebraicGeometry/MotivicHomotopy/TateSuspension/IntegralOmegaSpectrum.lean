/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.IntegralCoefficientSuspension
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.MotivicBonding
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.OmegaSpectrum

/-!
# The integral motivic Eilenberg–Mac Lane Ω-spectrum

Each integral level is the original A¹-local cochain representative in
bidegree `(2q,q)`. Its actual Tate bonding map represents the
signed coefficient suspension on reduced motivic cohomology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

/-- Tate suspension raises the cohomological degree by two on the levels. -/
theorem tateNextLevelDegree (q : ℕ) :
    2 * (q : ℤ) + 2 = 2 * ((q + 1 : ℕ) : ℤ) := by omega

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "Qₖ" => toAffineLineHomotopyCategory Sₖ
local notation "T" => tatePresheafSuspension Rₖ
local notation "E" => motivicReducedDerivedChains k

private abbrev integralLevel (q : ℕ) : AffineLineHomotopyCategory Sₖ :=
  motivicAffineLineRepresentative k (2 * (q : ℤ)) q

private def integralSuspensionOnRepresentatives (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    ((Qₖ).obj X ⟶ integralLevel k q) ≃
      ((Qₖ).obj ((T).obj X) ⟶ integralLevel k (q + 1)) := by
  let m : ℤ := 2 * (q : ℤ)
  let a := motivicAffineLineRepresentativeHomEquiv k m q X
  let b := integralTateSuspensionHomEquiv k X m q
  let c := motivicAffineLineRepresentativeHomEquiv k (2 * ((q + 1 : ℕ) : ℤ))
    (q + 1) ((T).obj X)
  let L := DerivedCategory.Q.obj (motivicSheafComplex k (q + 1))
  let d := eqToIso (congrArg (fun n : ℤ => L⟦n⟧) (tateNextLevelDegree q))
  exact a.trans (b.trans (d.homToEquiv.trans c.symm))

private theorem integralSuspensionOnRepresentatives_naturality (q : ℕ)
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    (g : (Qₖ).obj Y ⟶ integralLevel k q) :
    integralSuspensionOnRepresentatives k q X ((Qₖ).map f ≫ g) =
      (Qₖ).map ((T).map f) ≫ integralSuspensionOnRepresentatives k q Y g := by
  let m : ℤ := 2 * (q : ℤ)
  let m' : ℤ := 2 * ((q + 1 : ℕ) : ℤ)
  let c := motivicAffineLineRepresentativeHomEquiv k m' (q + 1) ((T).obj X)
  let c' := motivicAffineLineRepresentativeHomEquiv k m' (q + 1) ((T).obj Y)
  let L := DerivedCategory.Q.obj (motivicSheafComplex k (q + 1))
  let d := eqToIso (congrArg (fun n : ℤ => L⟦n⟧) (tateNextLevelDegree q))
  let a := motivicAffineLineRepresentativeHomEquiv k m q Y g
  apply c.injective
  have h : c ((Qₖ).map ((T).map f) ≫ integralSuspensionOnRepresentatives k q Y g) =
      (E).map ((T).map f) ≫ c' (integralSuspensionOnRepresentatives k q Y g) :=
    motivicAffineLineRepresentativeHomEquiv_precomp k m' (q + 1) ((T).map f) _
  rw [h]
  let cX := motivicAffineLineRepresentativeHomEquiv k (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) ((T).obj X)
  let cY := motivicAffineLineRepresentativeHomEquiv k (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) ((T).obj Y)
  let aX := motivicAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q X
  let bX := integralTateSuspensionHomEquiv k X (2 * (q : ℤ)) q
  let bY := integralTateSuspensionHomEquiv k Y (2 * (q : ℤ)) q
  change cX (cX.symm (d.homToEquiv (bX (aX ((Qₖ).map f ≫ g))))) =
    (E).map ((T).map f) ≫ cY (cY.symm (d.homToEquiv (bY a)))
  rw [cX.apply_symm_apply, cY.apply_symm_apply]
  have ha : aX ((Qₖ).map f ≫ g) = (E).map f ≫ a :=
    motivicAffineLineRepresentativeHomEquiv_precomp k (2 * (q : ℤ)) q f g
  rw [ha]
  change integralTateSuspensionHomEquiv k X m q ((E).map f ≫ a) ≫ d.hom =
    (E).map ((T).map f) ≫ integralTateSuspensionHomEquiv k Y m q a ≫ d.hom
  exact (congrArg (· ≫ d.hom) (integralTateSuspensionHomEquiv_precomp k f m q a)).trans
    (Category.assoc _ _ _)

/-- The integral Tate prespectrum has the original motivic Eilenberg–Mac Lane levels. -/
@[no_expose, colib_tag "COL-1117"]
def integralMotivicTatePrespectrum : A1TatePrespectrum Rₖ where
  level := integralLevel k
  bonding q := tateBondingMap Rₖ (integralLevel k q) (integralLevel k (q + 1))
    (fun X => integralSuspensionOnRepresentatives k q X)
    (fun f g => integralSuspensionOnRepresentatives_naturality k q f g)

/-- The integral level is the original A¹-local representative of bidegree `(2q,q)`. -/
theorem integralMotivicTatePrespectrum_level (q : ℕ) :
    (integralMotivicTatePrespectrum k).level q =
      motivicAffineLineRepresentative k (2 * (q : ℤ)) q := by
  unfold integralMotivicTatePrespectrum
  rfl

private theorem integralBonding_apply (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (f : (Qₖ).obj X ⟶ integralLevel k q) :
    tateSuspensionHomComparison Rₖ (integralLevel k (q + 1)) X
      ((motivicTateSuspension Rₖ).map f ≫ (integralMotivicTatePrespectrum k).bonding q) =
      integralSuspensionOnRepresentatives k q X f := by
  unfold integralMotivicTatePrespectrum
  exact tateSuspensionHomComparison_tateBondingMap Rₖ _ _ _ _ X f

/-- Integral Tate bonding represents the signed coefficient suspension on the
original pointed source, with the next cohomological degree identified. -/
@[colib_tag "COL-1117"]
theorem integralMotivicTatePrespectrum_bonding_cohomology (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ)
    (f : (Qₖ).obj X ⟶ motivicAffineLineRepresentative k (2 * (q : ℤ)) q) :
    let A := motivicAffineLineRepresentative k (2 * ((q + 1 : ℕ) : ℤ)) (q + 1)
    let e := eqToHom (integralMotivicTatePrespectrum_level k q).symm
    let e' := eqToHom (integralMotivicTatePrespectrum_level k (q + 1))
    let L := DerivedCategory.Q.obj (motivicSheafComplex k (q + 1))
    let d := eqToHom (congrArg (fun n : ℤ => L⟦n⟧) (tateNextLevelDegree q))
    motivicAffineLineRepresentativeHomEquiv k (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) ((T).obj X)
        (tateSuspensionHomComparison Rₖ A X
          ((motivicTateSuspension Rₖ).map (f ≫ e) ≫
            (integralMotivicTatePrespectrum k).bonding q ≫ e')) =
      integralTateSuspensionHomEquiv k X (2 * (q : ℤ)) q
        (motivicAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q X f) ≫ d := by
  intro A e e' L d
  let F := motivicTateSuspension Rₖ
  let h := (integralMotivicTatePrespectrum k).bonding q
  have he : F.map (f ≫ e) ≫ h ≫ e' = F.map f ≫ h := by
    change F.map (f ≫ 𝟙 _) ≫ h ≫ 𝟙 _ = F.map f ≫ h
    rw [Category.comp_id, Category.comp_id]
  have h₀ : tateSuspensionHomComparison Rₖ A X (F.map f ≫ h) =
      integralSuspensionOnRepresentatives k q X f := integralBonding_apply k q X f
  rw [he, h₀]
  let c := motivicAffineLineRepresentativeHomEquiv k (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) ((T).obj X)
  let j := eqToIso (congrArg (fun n : ℤ => L⟦n⟧) (tateNextLevelDegree q))
  let g := integralTateSuspensionHomEquiv k X (2 * (q : ℤ)) q
    (motivicAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q X f)
  change c (c.symm (j.homToEquiv g)) = j.homToEquiv g
  exact c.apply_symm_apply _

/-- The actual integral adjoint bonding maps are invertible in A¹-homotopy. -/
@[colib_tag "COL-1117", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, Theorem 2.4, pp. 5–6" "adaptation"
  "Tate suspension for the integral cochain representatives gives the adjoint bonding isomorphism"]
theorem integralMotivicTatePrespectrum_isOmegaSpectrum :
    SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction Rₖ)
      (integralMotivicTatePrespectrum k) := by
  apply isOmegaSpectrum_of_bijective_bonding
  intro q X
  let b := integralSuspensionOnRepresentatives k q X
  let c := tateSuspensionHomComparison Rₖ (integralLevel k (q + 1)) X
  let p := fun f : (Qₖ).obj X ⟶ integralLevel k q =>
    (motivicTateSuspension Rₖ).map f ≫ (integralMotivicTatePrespectrum k).bonding q
  have h : c ∘ p = b := by
    funext f
    exact integralBonding_apply k q X f
  change Function.Bijective p
  apply (Function.Bijective.of_comp_iff' c.bijective p).1
  rw [h]
  exact b.bijective

/-- The actual integral Eilenberg–Mac Lane Tate Ω-spectrum. -/
@[colib_tag "COL-1117"]
def integralMotivicTateOmegaSpectrum : MotivicTateOmegaSpectrum Rₖ :=
  ⟨integralMotivicTatePrespectrum k, integralMotivicTatePrespectrum_isOmegaSpectrum k⟩

end AlgebraicGeometry.MotivicHomotopy
