/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Smooth.PolynomialProjection
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.CylinderCriterion
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Representatives.Affine
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Representatives.Polynomial
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.PrincipalCoefficient

/-!
# The original polynomial representatives for whole-cylinder lifting

The coefficient restriction retains both representatives, their full marked
fiber, and the actual cylinder maps. A lift for those polynomial data yields
a lift on the whole native cylinder over the original base open.

Adapted from `Motivic/Cohomology/A1/Sheafification/WholeCylinderLifting.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

open scoped Polynomial

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "proj" => projection (SmoothSite.additiveGroupObject (Spec (.of k)))

section Polynomial

variable (R : Type u) [CommRing R] (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]

local notation "q" => (polynomialProjection (.of R))

local instance : SmoothOfRelativeDimension 1 q :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R
local instance : Smooth q := SmoothOfRelativeDimension.smooth 1 q

/-- Lifting two matching original sections from their literal polynomial representatives. -/
def NativePolynomialRepresentativeLifting (Pst : PresheafWithTransfers.{u + 1} k) : Prop :=
  ∀ {X U T Ao Yo Bo : SmoothSite (Spec (.of k))}
    (jU : U ⟶ X) [IsOpenImmersion jU.left]
    (l₀ : SmoothSite.mk t ⟶ U) [IsOpenImmersion l₀.left]
    (eT : T ≅ affineLineCylinder.obj U) (m₀ : SmoothSite.mk (q ≫ t) ⟶ T)
    (_H₀ : IsPullback (m₀ ≫ eT.hom).left q ((proj).app U).left l₀.left)
    (i : Ao ⟶ T) (v : Yo ⟶ T) (bA : Bo ⟶ Ao) (bY : Bo ⟶ Yo) (_HB : IsPullback bA bY i v)
    {A Y Z : Scheme.{u}} [IsAffine A] [IsAffine Y]
    (a : A ⟶ Spec (.of R[X])) [IsOpenImmersion a]
    (p : Y ⟶ Spec (.of R[X])) [Etale p]
    (z : Z ⟶ Spec (.of R[X])) [IsClosedImmersion z] [IsFinite (z ≫ q)]
    (s : Z ⟶ Y) (_hs : s ≫ p = z) (_H : IsPullback s (𝟙 Z) p z)
    (_hcomp : Set.range z = (Set.range a)ᶜ)
    (rA₀ : A ⟶ Ao.left) (rY₀ : Y ⟶ Yo.left)
    (_hA₀ : rA₀ ≫ i.left = a ≫ m₀.left) (_hY₀ : rY₀ ≫ v.left = p ≫ m₀.left)
    (σ : ((nisnevichSheafify k).obj Pst).obj.sections (Cor.mk (affineLineCylinder.obj X)))
    (sA : (nisnevichImage Pst).sections (Cor.mk Ao))
    (sY : (nisnevichImage Pst).sections (Cor.mk Yo))
    (_hm : (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map bA) sA =
      (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map bY) sY)
    (_hsA : (nisnevichImageι Pst).hom.app (op (Cor.mk Ao)) sA =
      ((nisnevichSheafify k).obj Pst).obj.transfer
        ((Cor.graphFunctor k).map (i ≫ eT.hom ≫ affineLineCylinder.map jU)) σ)
    (_hsY : (nisnevichImageι Pst).hom.app (op (Cor.mk Yo)) sY =
      ((nisnevichSheafify k).obj Pst).obj.transfer
        ((Cor.graphFunctor k).map (v ≫ eT.hom ≫ affineLineCylinder.map jU)) σ),
    ∃ (W : SmoothSite (Spec (.of k))) (j : W ⟶ X),
      IsOpenImmersion j.left ∧ Nonempty W.left ∧
      ∃ z : (nisnevichImage Pst).sections (Cor.mk (affineLineCylinder.obj W)),
        (nisnevichImageι Pst).hom.app (op (Cor.mk (affineLineCylinder.obj W))) z =
          ((nisnevichSheafify k).obj Pst).obj.transfer
            ((Cor.graphFunctor k).map (affineLineCylinder.map j)) σ

end Polynomial

set_option maxHeartbeats 600000 in
-- The original affine representative refinement determines the cylinder maps.
/-- The exact polynomial lifting property gives a whole-cylinder lift. -/
theorem modelWholeCylinderLifting_of_nativePolynomialRepresentativeLifting
    (P : PresheafWithTransfers.{u + 1} k)
    (lift : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      [Algebra k R] [Algebra.FiniteType k R] (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t],
      NativePolynomialRepresentativeLifting R t P) :
    ModelWholeCylinderLifting P := by
  classical
  intro X _ _ σ
  obtain ⟨U, j, hj, hUn, hUa, T, e, A, Y, a, p, hAa, ha, hp, -, Z, z,
    hzc, hzf, hcomp, hYZ, B, bA, bY, HB, sA, sY, hm, hsA, hsY,
    r, hr, W, hWa, hW, s₀, -, H₀, -, -, -⟩ :=
      exists_affine_refined_distinguished_nisnevichImage_representatives P X σ
  let := hUa
  let := hj
  let := hUn
  let : IsIntegral U.left := isIntegral_of_isOpenImmersion j.left
  let := hAa
  let := ha
  let := hp
  let := hzc
  let := hYZ
  let : IsAffine W.toScheme := hWa
  let R := Γ(U.left, ⊤)
  let B₀ := principalCoefficientOpen U r
  let : IsAffine B₀.toScheme := by
    change IsAffineOpen (principalCoefficientOpen U r)
    exact IsAffineOpen.Spec_basicOpen (R := Γ(U.left, ⊤)) r
  let R₀ := Γ(B₀.toScheme, ⊤)
  obtain ⟨hDomain, hNormal, hNoetherian⟩ := principalCoefficientRing_properties U r hr
  let : IsDomain R₀ := hDomain
  let : IsIntegrallyClosed R₀ := hNormal
  let : IsNoetherianRing R₀ := hNoetherian
  let q₀ := e.hom.left ≫ ((proj).app U).left ≫ U.left.isoSpec.hom
  let eN := originalCylinderNativeIso U T e
  let heN := originalCylinderNativeIso_projection U T e
  let c₀ := B₀.toScheme.isoSpec.inv ≫ B₀.ι
  let l₀S := c₀ ≫ U.left.isoSpec.inv
  let : IsOpenImmersion l₀S := by
    dsimp only [l₀S, c₀]
    infer_instance
  let t₀ := l₀S ≫ U.hom
  let : Smooth t₀ := inferInstanceAs (Smooth (l₀S ≫ U.hom))
  let : Algebra k R₀ := (Spec.preimage t₀).hom.toAlgebra
  let : Algebra.FiniteType k R₀ := by
    apply RingHom.finiteType_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  let qN := polynomialProjection (.of R₀)
  let : SmoothOfRelativeDimension 1 qN :=
    AffineLineEtaleCompactification.polynomialProjection_smooth_one R₀
  let : Smooth qN := SmoothOfRelativeDimension.smooth 1 qN
  obtain ⟨l₀, m₀, hl₀, Hmodel, -, -, hA₀, hY₀⟩ :=
    exists_polynomialRepresentativeRefinement (k := k) U T e B₀ a.left p.left W hW t₀
      (Category.assoc c₀ U.left.isoSpec.inv U.hom)
  let := hl₀
  let a₀ := originalAffineRefinedNativePuncture R eN q₀ heN B₀ a.left
  let p₀ := originalAffineRefinedNativeMap R eN q₀ heN B₀ p.left W hW
  let z₀ := originalAffineRefinedNativeMarked R eN q₀ heN B₀ z
  let : IsAffine ((a.left ≫ q₀) ⁻¹ᵁ B₀).toScheme :=
    originalAffineRefinedNativePuncture_affine R eN q₀ heN B₀ a.left
  let : IsFinite (z ≫ q₀) := by
    let : IsFinite (z ≫ e.hom.left ≫ ((proj).app U).left) := hzf
    simpa only [q₀, Category.assoc] using
      (inferInstanceAs (IsFinite
        ((z ≫ e.hom.left ≫ ((proj).app U).left) ≫ U.left.isoSpec.hom)))
  let : IsOpenImmersion a₀ := inferInstanceAs
    (IsOpenImmersion (originalAffineRefinedNativePuncture R eN q₀ heN B₀ a.left))
  let : Etale p₀ := inferInstanceAs
    (Etale (originalAffineRefinedNativeMap R eN q₀ heN B₀ p.left W hW))
  let : IsClosedImmersion z₀ := inferInstanceAs
    (IsClosedImmersion (originalAffineRefinedNativeMarked R eN q₀ heN B₀ z))
  let : IsFinite (z₀ ≫ qN) := inferInstanceAs (IsFinite
    (originalAffineRefinedNativeMarked R eN q₀ heN B₀ z ≫ polynomialProjection (.of R₀)))
  have Hmark : IsPullback s₀ (𝟙 _) p₀ z₀ :=
    originalAffineRefinedNativeMarked_isPullback R eN q₀ heN B₀ p.left W hW z s₀ H₀
  have hs₀ : s₀ ≫ p₀ = z₀ := by simpa only [Category.id_comp] using Hmark.w
  have hcomp₀ : Set.range z₀ = (Set.range a₀)ᶜ :=
    originalAffineRefinedNative_complement R eN q₀ heN B₀ a.left z hcomp
  let rA₀ := ((a.left ≫ q₀) ⁻¹ᵁ B₀).ι
  let rY₀ := W.ι
  exact lift R₀ t₀ j l₀ e m₀ Hmodel
    a p bA bY HB a₀ p₀ z₀ s₀ hs₀ Hmark hcomp₀ rA₀ rY₀ hA₀ hY₀
    σ sA sY hm hsA hsY

end AlgebraicGeometry.PresheafWithTransfers
