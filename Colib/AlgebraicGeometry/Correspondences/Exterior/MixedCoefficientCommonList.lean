/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientExchange
public import Colib.AlgebraicGeometry.Intersection.SmoothDiagonalGraphList

/-!
# A common diagonal family on the literal mixed coefficient scheme

Put `M = X × U` and `K = W × T`. The literal coefficient scheme is
`C = (X × T) × (W × U)`, with its previously constructed middle pair
`m : C ⟶ M × M`. The middle factor exchange `σ` fixes the diagonal.
Consequently the diagonal is a section of the smooth map `σ ≫ pr₁`.

Native pullback isomorphisms and the actual coefficient factor exchange identify
`C` with the pullback of this smooth map along `(p,ψ) : K ⟶ M`. The first
projection of that pullback is exactly `m`, not merely a map agreeing on reduced
points. The common-section theorem therefore constructs a single regular
diagonal-kernel family whose literal image in `𝒪_{C,c}` is also regular.

The base is locally Noetherian, so every actual closed support `W` and its
product with `T` are locally Noetherian. No flatness of `ψ` or the support
projection, integrality, compatible-component condition, or Tor hypothesis is
used. The original `Fin r` order and the literal signs in `m*` are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S : Scheme.{u}} (X Y T U : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) (ψ : T ⟶ U)

local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "σ" => nativeMixedMiddleSwap X U
local notation3 (prettyPrint := false) "φ" => nativeMixedSupportMap X Y T U W ψ
local notation3 (prettyPrint := false) "m" => nativeMixedCoefficientPair X Y T U W ψ

/-- The smooth projection obtained by the actual middle factor exchange. -/
def nativeMixedSectionProjection : pullback g g ⟶ (SmoothSite.product X U).left :=
  (σ).hom ≫ pullback.fst g g

/-- The exchanged projection is smooth because the exchange is an isomorphism. -/
instance nativeMixedSectionProjection_smooth : Smooth (nativeMixedSectionProjection X U) := by
  dsimp [nativeMixedSectionProjection]
  infer_instance

/-- The actual diagonal remains a section after the middle factor exchange. -/
@[reassoc (attr := simp)]
theorem diagonal_nativeMixedSectionProjection :
    pullback.diagonal (pullback.fst X.hom U.hom ≫ X.hom) ≫
      nativeMixedSectionProjection X U =
      𝟙 (SmoothSite.product X U).left := by
  change pullback.diagonal g ≫ nativeMixedSectionProjection X U = _
  have diagonalSwap := diagonal_nativeMixedMiddleSwap X U
  change pullback.diagonal g ≫ (σ).hom = _ at diagonalSwap
  rw [nativeMixedSectionProjection, ← Category.assoc, diagonalSwap,
    pullback.diagonal_fst]
  rfl

/-- The literal mixed coefficient scheme is the actual base change of the
exchanged smooth projection along the arbitrary support/parameter map. -/
def nativeMixedCoefficientSectionIso : nativeMixedCoefficient X Y T U W ≅
    pullback (nativeMixedSectionProjection X U) φ :=
  nativeMixedCoefficientGraphIso X Y T U W ψ ≪≫
    (Scheme.Hom.diagonalBaseChangeGraphIso g φ).symm ≪≫
    asIso (pullback.map (pullback.fst g g) φ (nativeMixedSectionProjection X U) φ
      (σ).inv (𝟙 _) (𝟙 _) (by simp [nativeMixedSectionProjection]) (by simp))

/-- The first projection under the constructed isomorphism is precisely the
original mixed pair. This equality fixes the resulting stalk scalar map. -/
@[reassoc]
theorem nativeMixedCoefficientSectionIso_hom_fst :
    (nativeMixedCoefficientSectionIso X Y T U W ψ).hom ≫
      pullback.fst (nativeMixedSectionProjection X U) φ = m := by
  simp only [nativeMixedCoefficientSectionIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, Category.assoc, pullback.map, pullback.lift_fst]
  rw [Scheme.Hom.diagonalBaseChangeGraphIso_inv_fst_assoc]
  change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
    nativeMixedGraphPair X Y T U W ψ ≫ (σ).inv = m
  rw [← Category.assoc, ← nativeMixedCoefficientPair_exchange, Category.assoc]
  simp

/-- A locally Noetherian base makes the actual support/parameter source locally
Noetherian. This uses the closed support, not a flatness assumption on its projection. -/
theorem isLocallyNoetherian_nativeMixedSupport [IsLocallyNoetherian S] :
    IsLocallyNoetherian (exteriorIdentitySupport X Y T W) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (show X.left ⟶ S from X.hom)
  have : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.hom Y.hom)
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian W.subschemeι
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)

/-- One native diagonal-kernel family is regular in both the actual middle
stalk and the literal mixed coefficient stalk. The arbitrary parameter map is
not assumed flat, and no common-list or Tor provider is an input. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/ProductTransversality.lean:313-364"
  "specialization" "Locally Noetherian base; actual mixed coefficient product and middle \
    pair, with one ordered regular diagonal-kernel family constructed by native \
    smooth-section base change"]
theorem exists_nativeMixedCoefficient_common_regular_list [IsLocallyNoetherian S]
    (c : nativeMixedCoefficient X Y T U W) (v : (SmoothSite.product X U).left)
    (hc : m c = pullback.diagonal g v) :
    ∃ (r : ℕ) (b : Fin r → (pullback g g).presheaf.stalk (m c)),
      IsRegular ((pullback g g).presheaf.stalk (m c)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        (((pullback g g).presheaf.stalkCongr (.of_eq hc)).hom ≫
          (pullback.diagonal g).stalkMap v).hom ∧
      IsRegular ((nativeMixedCoefficient X Y T U W).presheaf.stalk c)
        (List.ofFn (fun i => ((m).stalkMap c).hom (b i))) := by
  have : IsLocallyNoetherian (exteriorIdentitySupport X Y T W) :=
    isLocallyNoetherian_nativeMixedSupport X Y T W
  let e := nativeMixedCoefficientSectionIso X Y T U W ψ
  have he : e.hom ≫ pullback.fst (nativeMixedSectionProjection X U) φ = m :=
    nativeMixedCoefficientSectionIso_hom_fst X Y T U W ψ
  revert hc
  rw [← he]
  intro hc
  exact Scheme.Hom.exists_isRegular_stalkList_pullbackIso_of_smooth_section
    (nativeMixedSectionProjection X U) (pullback.diagonal g)
    (diagonal_nativeMixedSectionProjection X U) φ e c v hc

end Stacks.Chow
