/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.FiniteCoefficientSuspension
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.IntegralOmegaSpectrum

/-!
# The finite motivic Eilenberg–Mac Lane Ω-spectrum

Each finite coefficient level is the original A¹-local cochain representative in
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

private abbrev finiteLevel (n q : ℕ) : AffineLineHomotopyCategory Sₖ :=
  motivicFiniteAffineLineRepresentative k (2 * (q : ℤ)) q n

private def finiteSuspensionOnRepresentatives (q n : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    ((Qₖ).obj X ⟶ finiteLevel k n q) ≃
      ((Qₖ).obj ((T).obj X) ⟶ finiteLevel k n (q + 1)) := by
  let m : ℤ := 2 * (q : ℤ)
  let a := motivicFiniteAffineLineRepresentativeHomEquiv k m q n X
  let b := finiteTateSuspensionHomEquiv k X m q n
  let c := motivicFiniteAffineLineRepresentativeHomEquiv k (2 * ((q + 1 : ℕ) : ℤ))
    (q + 1) n ((T).obj X)
  let L := DerivedCategory.Q.obj (motivicFiniteSheafComplex k (q + 1) n)
  let d := eqToIso (congrArg (fun i : ℤ => L⟦i⟧) (tateNextLevelDegree q))
  exact a.trans (b.trans (d.homToEquiv.trans c.symm))

private theorem finiteSuspensionOnRepresentatives_naturality (q n : ℕ)
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    (g : (Qₖ).obj Y ⟶ finiteLevel k n q) :
    finiteSuspensionOnRepresentatives k q n X ((Qₖ).map f ≫ g) =
      (Qₖ).map ((T).map f) ≫ finiteSuspensionOnRepresentatives k q n Y g := by
  let m : ℤ := 2 * (q : ℤ)
  let m' : ℤ := 2 * ((q + 1 : ℕ) : ℤ)
  let c := motivicFiniteAffineLineRepresentativeHomEquiv k m' (q + 1) n ((T).obj X)
  let c' := motivicFiniteAffineLineRepresentativeHomEquiv k m' (q + 1) n ((T).obj Y)
  let L := DerivedCategory.Q.obj (motivicFiniteSheafComplex k (q + 1) n)
  let d := eqToIso (congrArg (fun i : ℤ => L⟦i⟧) (tateNextLevelDegree q))
  let a := motivicFiniteAffineLineRepresentativeHomEquiv k m q n Y g
  apply c.injective
  have h : c ((Qₖ).map ((T).map f) ≫ finiteSuspensionOnRepresentatives k q n Y g) =
      (E).map ((T).map f) ≫ c' (finiteSuspensionOnRepresentatives k q n Y g) :=
    motivicFiniteAffineLineRepresentativeHomEquiv_precomp k m' (q + 1) n ((T).map f) _
  rw [h]
  let cX := motivicFiniteAffineLineRepresentativeHomEquiv k m' (q + 1) n ((T).obj X)
  let cY := motivicFiniteAffineLineRepresentativeHomEquiv k m' (q + 1) n ((T).obj Y)
  let aX := motivicFiniteAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q n X
  let bX := finiteTateSuspensionHomEquiv k X (2 * (q : ℤ)) q n
  let bY := finiteTateSuspensionHomEquiv k Y (2 * (q : ℤ)) q n
  change cX (cX.symm (d.homToEquiv (bX (aX ((Qₖ).map f ≫ g))))) =
    (E).map ((T).map f) ≫ cY (cY.symm (d.homToEquiv (bY a)))
  rw [cX.apply_symm_apply, cY.apply_symm_apply]
  have ha : aX ((Qₖ).map f ≫ g) = (E).map f ≫ a :=
    motivicFiniteAffineLineRepresentativeHomEquiv_precomp k (2 * (q : ℤ)) q n f g
  rw [ha]
  change finiteTateSuspensionHomEquiv k X m q n ((E).map f ≫ a) ≫ d.hom =
    (E).map ((T).map f) ≫ finiteTateSuspensionHomEquiv k Y m q n a ≫ d.hom
  exact (congrArg (· ≫ d.hom) (finiteTateSuspensionHomEquiv_precomp k f m q n a)).trans
    (Category.assoc _ _ _)

/-- The finite Tate prespectrum uses the actual multiplication-cone coefficients. -/
@[no_expose, colib_tag "COL-1117"]
def finiteMotivicTatePrespectrum (n : ℕ) : A1TatePrespectrum Rₖ where
  level := finiteLevel k n
  bonding q := tateBondingMap Rₖ (finiteLevel k n q) (finiteLevel k n (q + 1))
    (fun X => finiteSuspensionOnRepresentatives k q n X)
    (fun f g => finiteSuspensionOnRepresentatives_naturality k q n f g)

/-- The finite level is the original A¹-local representative of its coefficient cone. -/
theorem finiteMotivicTatePrespectrum_level (n q : ℕ) :
    (finiteMotivicTatePrespectrum k n).level q =
      motivicFiniteAffineLineRepresentative k (2 * (q : ℤ)) q n := by
  unfold finiteMotivicTatePrespectrum
  rfl

private theorem finiteBonding_apply (q n : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (f : (Qₖ).obj X ⟶ finiteLevel k n q) :
    tateSuspensionHomComparison Rₖ (finiteLevel k n (q + 1)) X
      ((motivicTateSuspension Rₖ).map f ≫ (finiteMotivicTatePrespectrum k n).bonding q) =
      finiteSuspensionOnRepresentatives k q n X f := by
  unfold finiteMotivicTatePrespectrum
  exact tateSuspensionHomComparison_tateBondingMap Rₖ _ _ _ _ X f

/-- Finite Tate bonding represents the suspension induced by the
actual signed multiplication-cone map. -/
@[colib_tag "COL-1117"]
theorem finiteMotivicTatePrespectrum_bonding_cohomology (q n : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ)
    (f : (Qₖ).obj X ⟶ motivicFiniteAffineLineRepresentative k (2 * (q : ℤ)) q n) :
    let A := motivicFiniteAffineLineRepresentative k (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) n
    let e := eqToHom (finiteMotivicTatePrespectrum_level k n q).symm
    let e' := eqToHom (finiteMotivicTatePrespectrum_level k n (q + 1))
    let L := DerivedCategory.Q.obj (motivicFiniteSheafComplex k (q + 1) n)
    let d := eqToHom (congrArg (fun i : ℤ => L⟦i⟧) (tateNextLevelDegree q))
    motivicFiniteAffineLineRepresentativeHomEquiv k
        (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) n ((T).obj X)
        (tateSuspensionHomComparison Rₖ A X
          ((motivicTateSuspension Rₖ).map (f ≫ e) ≫
            (finiteMotivicTatePrespectrum k n).bonding q ≫ e')) =
      finiteTateSuspensionHomEquiv k X (2 * (q : ℤ)) q n
        (motivicFiniteAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q n X f) ≫ d := by
  intro A e e' L d
  let F := motivicTateSuspension Rₖ
  let h := (finiteMotivicTatePrespectrum k n).bonding q
  have he : F.map (f ≫ e) ≫ h ≫ e' = F.map f ≫ h := by
    change F.map (f ≫ 𝟙 _) ≫ h ≫ 𝟙 _ = F.map f ≫ h
    rw [Category.comp_id, Category.comp_id]
  have h₀ : tateSuspensionHomComparison Rₖ A X (F.map f ≫ h) =
      finiteSuspensionOnRepresentatives k q n X f := finiteBonding_apply k q n X f
  rw [he, h₀]
  let c := motivicFiniteAffineLineRepresentativeHomEquiv k
    (2 * ((q + 1 : ℕ) : ℤ)) (q + 1) n ((T).obj X)
  let j := eqToIso (congrArg (fun i : ℤ => L⟦i⟧) (tateNextLevelDegree q))
  let g := finiteTateSuspensionHomEquiv k X (2 * (q : ℤ)) q n
    (motivicFiniteAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q n X f)
  change c (c.symm (j.homToEquiv g)) = j.homToEquiv g
  exact c.apply_symm_apply _

/-- The actual finite adjoint bonding maps are invertible in A¹-homotopy. -/
@[colib_tag "COL-1117", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, Theorem 2.4, pp. 5–6" "adaptation"
  "Tate suspension on the finite coefficient representatives gives the adjoint bonding isomorphism"]
theorem finiteMotivicTatePrespectrum_isOmegaSpectrum (n : ℕ) :
    SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction Rₖ)
      (finiteMotivicTatePrespectrum k n) := by
  apply isOmegaSpectrum_of_bijective_bonding
  intro q X
  let b := finiteSuspensionOnRepresentatives k q n X
  let c := tateSuspensionHomComparison Rₖ (finiteLevel k n (q + 1)) X
  let p := fun f : (Qₖ).obj X ⟶ finiteLevel k n q =>
    (motivicTateSuspension Rₖ).map f ≫ (finiteMotivicTatePrespectrum k n).bonding q
  have h : c ∘ p = b := by
    funext f
    exact finiteBonding_apply k q n X f
  change Function.Bijective p
  apply (Function.Bijective.of_comp_iff' c.bijective p).1
  rw [h]
  exact b.bijective

/-- The actual finite-coefficient Eilenberg–Mac Lane Tate Ω-spectrum. -/
@[colib_tag "COL-1117"]
def finiteMotivicTateOmegaSpectrum (n : ℕ) : MotivicTateOmegaSpectrum Rₖ :=
  ⟨finiteMotivicTatePrespectrum k n, finiteMotivicTatePrespectrum_isOmegaSpectrum k n⟩

end AlgebraicGeometry.MotivicHomotopy
