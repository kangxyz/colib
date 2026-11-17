/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientationChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.TrivialThomPowerBasic
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OpenRestrictionVanishing
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OrientationVanishing
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.VectorBundleFrameChange

/-! # Thom classes and shifted Hom vanishing for the original normal charts -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private def chartClassOfIso {C : Type*} [Category* C] {A B D K : C}
    (e : A ≅ B) (f : B ≅ D) (g : D ⟶ K) :
    { τ : A ⟶ K // τ = e.hom ≫ f.hom ≫ g } :=
  ⟨(e ≪≫ f).hom ≫ g, Category.assoc e.hom f.hom g⟩

variable (k : Type u) [Field k]

local notation "Base" => Spec (CommRingCat.of k)
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "E₀" => (Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules)
local notation "p" => normalBundleProjection i hX hZ
local notation "z" => normalBundleZeroSection i hX hZ
set_option quotPrecheck false in
local notation "j" => closedPairOpenInclusion (z).left

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The native abelian structure on transfer sheaves for the normal bundle charts. -/
local instance normalBundleOrientationLocalAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

local notation "P" => relativeOpenRestrictionMotive k (p) j
local notation "L" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)
set_option quotPrecheck false in
local notation "K" => (L).obj ((M).obj (base Base))

section ChartMotive

variable (V : Z.left.affineOpens)

set_option quotPrecheck false in
local notation "U" => (opensFunctor Z).obj V.1

/-- The chart motive is the normalized affine-space Thom motive over the chart base. -/
def normalBundleBasisThomIso
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) :
    (P).obj V.1 ≅ (L).obj ((M).obj U) := by
  letI : IsAffine (U).left := V.2
  exact (Φ).mapIso (normalBundleBasisArrowIso k i hX hZ V b) ≪≫
    effectiveAffineSpaceThomIso k U (n - m)

set_option maxHeartbeats 700000 in
-- Keep the original chart and affine comparisons fixed before pasting the class.
private def normalBundleBasisThomClassData
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) [IsAffine (U).left] :=
  chartClassOfIso ((Φ).mapIso (normalBundleBasisArrowIso k i hX hZ V b))
    (effectiveAffineSpaceThomIso k U (n - m)) ((L).map ((M).map (toBase U)))

/-- The supported orientation on one marked chart. -/
@[no_expose]
def normalBundleBasisThomClass
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) : (P).obj V.1 ⟶ K := by
  letI : IsAffine (U).left := V.2
  exact (normalBundleBasisThomClassData k i hX hZ V b).val

set_option maxHeartbeats 850000 in
-- The chart class and the original affine class use the same reflected pair objects.
/-- The local class is the pullback of the chosen affine-space class along the chart arrow. -/
theorem normalBundleBasisThomClass_eq_map
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) [IsAffine (U).left] :
    normalBundleBasisThomClass k i hX hZ V b =
      (Φ).map (normalBundleBasisArrowIso k i hX hZ V b).hom ≫
        effectiveAffineSpaceThomClass k U (n - m) :=
  (normalBundleBasisThomClassData k i hX hZ V b).property

end ChartMotive

section Vanishing

private theorem normalBundleBasisThomIso_shift_vanishing
    (W : Z.left.affineOpens)
    (bW : Module.Basis (Fin (n - m)) Γ(Z.left, W.1) Γ(E₀, W.1))
    (a : ℤ) (ha : 0 < a) : Subsingleton (((P).obj W.1)⟦a⟧ ⟶ K) := by
  let e := normalBundleBasisThomIso k i hX hZ W bW
  let f := (shiftFunctor (EffectiveMotivesMinus k) a).mapIso e
  have h := subsingleton_shift_iterateLefschetz_hom_base_of_pos
    k (n - m) ((opensFunctor Z).obj W.1) a ha
  exact ⟨fun f₀ f₁ => (cancel_epi f.inv).mp (h.elim (f.inv ≫ f₀) (f.inv ≫ f₁))⟩

set_option maxHeartbeats 750000 in
-- Install the effective triangulated category before using the affine cover.
/-- The negative-degree groups for the normal pair vanish over every open of
the centre. We use affine charts for the given bundle and descend along the
original binary relative triangles. -/
theorem normalBundleThomClass_shift_vanishing {J : Type*}
    (V : J → Z.left.affineOpens) (ts : Finset J)
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hc : ts.sup (fun x => (V x).1) = ⊤)
    (U : Z.left.Opens) (a : ℤ) (ha : 0 < a) :
    Subsingleton (((P).obj U)⟦a⟧ ⟶ K) := by
  let C := EffectiveMotivesMinus k
  let F : Z.left.Opens ⥤ C := P
  let A : C := K
  let : ∀ d : ℤ, (shiftFunctor C d).Additive := fun d => inferInstance
  let : Pretriangulated C := inferInstance
  have hzero : IsZero (F.obj ⊥) := isZero_relativeOpenRestrictionMotive_bot k (p) j
  have htri : ∀ V W : Z.left.Opens, BinaryRestrictionTriangle F V W :=
    relativeOpenRestrictionTriangle k (p) j
  have hchart (x : J) (W : Z.left.affineOpens) (h : W.1 ≤ (V x).1) (d : ℤ) (hd : 0 < d) :
      Subsingleton ((F.obj W.1)⟦d⟧ ⟶ A) :=
    normalBundleBasisThomIso_shift_vanishing k i hX hZ W
      (Scheme.Modules.vectorBundleBasisRestrict E₀ (b x) h) d hd
  exact subsingleton_shift_openRestriction_hom_of_affine_cover
    (E := C) k (B := Z) F A hzero htri
    (fun x => (V x).1) ts hc hchart U a ha

end Vanishing

end AlgebraicGeometry.MotivicHomotopy
