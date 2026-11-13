/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiber
public import Colib.AlgebraicGeometry.Scheme.AffinePullbackSections
public import Colib.RingTheory.Norm.MarkedFactor

/-!
# The norm on the full marked fiber of a finite morphism

The norm on the original affine chart restricts to its marked scalar when
the value on the entire residual fiber is one. The decomposition and the
algebra maps are those of the original Cartesian square.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Morphisms/Finite/Norm/MarkedFiber.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- The global sections of a coproduct as the concrete ring product. -/
def coproductGlobalSectionsIso (Z E : Scheme.{u}) :
    Γ(Z ⨿ E, ⊤) ≅ CommRingCat.of (Γ(Z, ⊤) × Γ(E, ⊤)) :=
  Scheme.coprodPresheafObjIso ⊤ ≪≫
    (prodIsProd Γ(Z, ⊤) Γ(E, ⊤)).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit Γ(Z, ⊤) Γ(E, ⊤))

@[reassoc]
theorem coproductGlobalSectionsIso_fst (Z E : Scheme.{u}) :
    (coproductGlobalSectionsIso Z E).hom ≫ CommRingCat.ofHom (RingHom.fst _ _) =
      (coprod.inl : Z ⟶ Z ⨿ E).appTop := by
  dsimp only [coproductGlobalSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (CommRingCat.prodFan Γ(Z, ⊤) Γ(E, ⊤)).π.app
    (Discrete.mk WalkingPair.left) = _
  rw [IsLimit.conePointUniqueUpToIso_hom_comp]
  exact Scheme.coprodPresheafObjIso_hom_fst ⊤

@[reassoc]
theorem coproductGlobalSectionsIso_snd (Z E : Scheme.{u}) :
    (coproductGlobalSectionsIso Z E).hom ≫ CommRingCat.ofHom (RingHom.snd _ _) =
      (coprod.inr : E ⟶ Z ⨿ E).appTop := by
  dsimp only [coproductGlobalSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (CommRingCat.prodFan Γ(Z, ⊤) Γ(E, ⊤)).π.app
    (Discrete.mk WalkingPair.right) = _
  rw [IsLimit.conePointUniqueUpToIso_hom_comp]
  exact Scheme.coprodPresheafObjIso_hom_snd ⊤

section Marked

variable {T W Y Z : Scheme.{u}} (p : T ⟶ W) [IsFinite p]
  (j : Y ⟶ T) [IsOpenImmersion j] (z : Z ⟶ W) (s : Z ⟶ Y)
  (hs : (s ≫ j) ≫ p = z) (H : IsPullback s (𝟙 Z) (j ≫ p) z)

local notation "E" => (residualMarkedFiberOpen p j z s hs)
local notation "p₀" => (pullback.snd p z)

/-- Global sections of the actual full fiber as the two original factors. -/
def markedFiberGlobalSectionsRingEquiv :
    Γ(pullback p z, ⊤) ≃+* Γ(Z, ⊤) × Γ((E).toScheme, ⊤) :=
  ((asIso (markedResidualFiberIso p j z s hs H).hom.appTop) ≪≫
    coproductGlobalSectionsIso Z (E).toScheme).commRingCatIsoToRingEquiv

@[simp]
theorem markedFiberGlobalSectionsRingEquiv_fst (b : Γ(pullback p z, ⊤)) :
    (markedFiberGlobalSectionsRingEquiv p j z s hs H b).1 =
      (markedFiberSection p j z s hs).appTop b := by
  have h := congrArg (fun v ↦ (markedResidualFiberIso p j z s hs H).hom.appTop ≫ v)
    (coproductGlobalSectionsIso_fst Z (E).toScheme)
  rw [← Hom.comp_appTop, markedResidualFiberIso_inl] at h
  exact congrArg (fun v ↦ v b) h

@[simp]
theorem markedFiberGlobalSectionsRingEquiv_snd (b : Γ(pullback p z, ⊤)) :
    (markedFiberGlobalSectionsRingEquiv p j z s hs H b).2 = (E).ι.appTop b := by
  have h := congrArg (fun v ↦ (markedResidualFiberIso p j z s hs H).hom.appTop ≫ v)
    (coproductGlobalSectionsIso_snd Z (E).toScheme)
  rw [← Hom.comp_appTop, markedResidualFiberIso_inr] at h
  exact congrArg (fun v ↦ v b) h

/-- The splitting respects the scalar action of the actual projection. -/
def markedFiberGlobalSectionsAlgEquiv :
    letI : Algebra Γ(Z, ⊤) Γ(pullback p z, ⊤) := (p₀).appTop.hom.toAlgebra
    letI : Algebra Γ(Z, ⊤) Γ((E).toScheme, ⊤) := ((E).ι ≫ p₀).appTop.hom.toAlgebra
    Γ(pullback p z, ⊤) ≃ₐ[Γ(Z, ⊤)] (Γ(Z, ⊤) × Γ((E).toScheme, ⊤)) := by
  letI : Algebra Γ(Z, ⊤) Γ(pullback p z, ⊤) := (p₀).appTop.hom.toAlgebra
  letI : Algebra Γ(Z, ⊤) Γ((E).toScheme, ⊤) := ((E).ι ≫ p₀).appTop.hom.toAlgebra
  refine { markedFiberGlobalSectionsRingEquiv p j z s hs H with commutes' := ?_ }
  intro a
  apply Prod.ext
  · change (markedFiberGlobalSectionsRingEquiv p j z s hs H (algebraMap Γ(Z, ⊤) _ a)).1 = a
    rw [markedFiberGlobalSectionsRingEquiv_fst]
    change ((p₀).appTop ≫ (markedFiberSection p j z s hs).appTop) a = a
    rw [← Hom.comp_appTop, markedFiberSection_snd]
    simp
  · change (markedFiberGlobalSectionsRingEquiv p j z s hs H (algebraMap Γ(Z, ⊤) _ a)).2 =
      algebraMap Γ(Z, ⊤) Γ((E).toScheme, ⊤) a
    rw [markedFiberGlobalSectionsRingEquiv_snd]
    rfl

include H in
/-- The original norm is read on the full marked factor after affine base change. -/
theorem affineNorm_eq_marked_value [IsAffine W] [IsAffine Z] (b : Γ(T, ⊤))
    (hresidual : (residualMarkedFiberMap p j z s hs).appTop b = 1) :
    letI : Algebra Γ(W, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(T, ⊤)],
      z.appTop (Algebra.norm Γ(W, ⊤) b) = (s ≫ j).appTop b := by
  dsimp only
  let : IsAffine T := isAffine_of_isAffineHom p
  let : Algebra Γ(W, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(W, ⊤) Γ(Z, ⊤) := z.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(pullback p z, ⊤) := (p₀).appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ((E).toScheme, ⊤) := ((E).ι ≫ p₀).appTop.hom.toAlgebra
  intro hfree
  let : Module.Free Γ(W, ⊤) Γ(T, ⊤) := hfree
  let : Module.Finite Γ(W, ⊤) Γ(T, ⊤) := p.finite_appTop
  let e := (affinePullbackSectionsComparison p z).1.trans
    (markedFiberGlobalSectionsAlgEquiv p j z s hs H)
  apply Algebra.norm_eq_marked_value_of_split_baseChange e b ((s ≫ j).appTop b)
  change markedFiberGlobalSectionsRingEquiv p j z s hs H
    ((affinePullbackSectionsComparison p z).1 ((1 : Γ(Z, ⊤)) ⊗ₜ[Γ(W, ⊤)] b)) =
      ((s ≫ j).appTop b, 1)
  rw [(affinePullbackSectionsComparison p z).2 b]
  apply Prod.ext
  · rw [markedFiberGlobalSectionsRingEquiv_fst]
    change ((pullback.fst p z).appTop ≫ (markedFiberSection p j z s hs).appTop) b = _
    rw [← Hom.comp_appTop, markedFiberSection_fst]
  · rw [markedFiberGlobalSectionsRingEquiv_snd]
    exact hresidual

end Marked

end AlgebraicGeometry.Scheme
