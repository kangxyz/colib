/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.KoszulDevissage
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductResidueLength
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductStalkLocalization
public import Colib.RingTheory.Tor.ExteriorEuler.TorEuler
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension

/-!
# Tor Euler coefficients of products of closed intersections

At a generic point of the product of two closed intersections, the product
stalk ambient is a flat localization of the two ambient stalks. The two
actual structure modules are scalar extensions of the corresponding exterior
tensors. Over an arbitrary field the full residue tensor length is retained;
over a perfect field the reduced-product specialization makes this factor one.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme BaseChangeStalk
open scoped TensorProduct

universe u

namespace Stacks.Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [PerfectField k]
variable {X Y A B C D P Q : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (a : A ⟶ X) (b : B ⟶ Y) (c : C ⟶ X) (d : D ⟶ Y)
  [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
  (p : P ⟶ X) (q : Q ⟶ Y) [IsClosedImmersion p] [IsClosedImmersion q]
  (u : P ⟶ A) (v : Q ⟶ B) (u' : P ⟶ C) (v' : Q ⟶ D)
  (hu : p = u ≫ a) (hv : q = v ≫ b) (hu' : p = u' ≫ c) (hv' : q = v' ≫ d)
  (z : genericPoints (pullback (C := Scheme) (p ≫ f) (q ≫ g)))

local notation "R" => pullback f g
local notation "a₀" => Scheme.Hom.productClosedMap f g a b
local notation "c₀" => Scheme.Hom.productClosedMap f g c d
local notation "m" => Scheme.Hom.productClosedMap f g p q
set_option quotPrecheck false in
local notation "w" => m z.val
local notation "s" => p ≫ f
local notation "t" => q ≫ g
set_option quotPrecheck false in
local notation "x" => pullback.fst s t z.val
set_option quotPrecheck false in
local notation "y" => pullback.snd s t z.val
set_option quotPrecheck false in
local notation "P₀" => (X).presheaf.stalk (p x)
set_option quotPrecheck false in
local notation "Q₀" => (Y).presheaf.stalk (q y)
set_option quotPrecheck false in
local notation "R₀" => (R).presheaf.stalk w

omit [PerfectField k] [IsClosedImmersion p] [IsClosedImmersion q] in
/-- First projection of the product of two original closed immersions. -/
theorem productClosedMap_fst_apply :
    pullback.fst f g w = p x := by
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun m' : pullback s t ⟶ X => m' z.val)
    (pullback.lift_fst _ _ _)

omit [PerfectField k] [IsClosedImmersion p] [IsClosedImmersion q] in
/-- Second projection of the product of two original closed immersions. -/
theorem productClosedMap_snd_apply :
    pullback.snd f g w = q y := by
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun m' : pullback s t ⟶ Y => m' z.val)
    (pullback.lift_snd _ _ _)

omit [PerfectField k] [IsClosedImmersion a] [IsClosedImmersion b]
  [IsClosedImmersion p] [IsClosedImmersion q] in
/-- The product of the two actual maps from the intersections to their closed supports. -/
def productIntersectionMap :
    pullback s t ⟶ pullback (a ≫ f) (b ≫ g) :=
  pullback.map s t _ _ u v (𝟙 _)
    (by rw [Category.comp_id, hu, Category.assoc])
    (by rw [Category.comp_id, hv, Category.assoc])

local notation "r" => productIntersectionMap f g a b p q u v hu hv
local notation "r'" => productIntersectionMap f g c d p q u' v' hu' hv'

omit [PerfectField k] [IsClosedImmersion a] [IsClosedImmersion b]
  [IsClosedImmersion p] [IsClosedImmersion q] in
/-- The named intersection points enter the ambient through the indicated product support. -/
theorem productIntersectionMap_eq : m = r ≫ a₀ := by
  apply pullback.hom_ext (f := f) (g := g)
  · simp only [Category.assoc, Scheme.Hom.productClosedMap, productIntersectionMap,
      pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, hu]
  · simp only [Category.assoc, Scheme.Hom.productClosedMap, productIntersectionMap,
      pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, hv]

omit [PerfectField k] [IsClosedImmersion a] [IsClosedImmersion b]
  [IsClosedImmersion p] [IsClosedImmersion q] in
/-- The two actual ambient maps have equal values at the named point. -/
theorem productIntersectionMap_point_eq : w = a₀ (r z.val) :=
  congrArg (fun m' : pullback s t ⟶ R => m' z.val)
    (productIntersectionMap_eq f g a b p q u v hu hv)

local notation "α" => transportedClosedStalkMap a (u x) (p x)
  (congrArg (fun m' : P ⟶ X => m' x) hu)
local notation "β" => transportedClosedStalkMap b (v y) (q y)
  (congrArg (fun m' : Q ⟶ Y => m' y) hv)
local notation "α'" => transportedClosedStalkMap c (u' x) (p x)
  (congrArg (fun m' : P ⟶ X => m' x) hu')
local notation "β'" => transportedClosedStalkMap d (v' y) (q y)
  (congrArg (fun m' : Q ⟶ Y => m' y) hv')
set_option quotPrecheck false in
local notation "α₀" => transportedClosedStalkMap a₀ (r z.val) w
  (productIntersectionMap_point_eq f g a b p q u v hu hv z)
set_option quotPrecheck false in
local notation "β₀" => transportedClosedStalkMap c₀ (r' z.val) w
  (productIntersectionMap_point_eq f g c d p q u' v' hu' hv' z)
set_option quotPrecheck false in
local notation "M" => (ModuleCat.restrictScalars α).obj
  (ModuleCat.of (A.presheaf.stalk (u x)) (A.presheaf.stalk (u x)))
set_option quotPrecheck false in
local notation "N" => (ModuleCat.restrictScalars β).obj
  (ModuleCat.of (B.presheaf.stalk (v y)) (B.presheaf.stalk (v y)))
set_option quotPrecheck false in
local notation "M'" => (ModuleCat.restrictScalars α').obj
  (ModuleCat.of (C.presheaf.stalk (u' x)) (C.presheaf.stalk (u' x)))
set_option quotPrecheck false in
local notation "N'" => (ModuleCat.restrictScalars β').obj
  (ModuleCat.of (D.presheaf.stalk (v' y)) (D.presheaf.stalk (v' y)))

private def torCongr {Ring : Type u} [CommRing Ring] {L L' K K' : ModuleCat.{u} Ring}
    (e : L ≅ L') (e' : K ≅ K') (n : ℕ) :
    (((Tor (ModuleCat Ring) n).obj L).obj K) ≅ (((Tor (ModuleCat Ring) n).obj L').obj K') :=
  ((Tor (ModuleCat Ring) n).mapIso e).app K ≪≫ ((Tor (ModuleCat Ring) n).obj L').mapIso e'

private theorem length_quotientTor_eq_length_closedStalks
    {A B X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    [IsClosedImmersion a] [IsClosedImmersion b]
    (p : X) (x' : A) (y' : B) (hx : p = a x') (hy : p = b y') (n : ℕ) :
    Module.length (X.presheaf.stalk p)
        (((Tor (ModuleCat (X.presheaf.stalk p)) n).obj
          (ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p ⧸
            IdealSheafData.stalk a.ker p))).obj
          (ModuleCat.of (X.presheaf.stalk p) (X.presheaf.stalk p ⧸
            IdealSheafData.stalk b.ker p))) =
      Module.length (X.presheaf.stalk p)
        (((Tor (ModuleCat (X.presheaf.stalk p)) n).obj
          ((ModuleCat.restrictScalars (transportedClosedStalkMap a x' p hx)).obj
            (ModuleCat.of (A.presheaf.stalk x') (A.presheaf.stalk x')))).obj
          ((ModuleCat.restrictScalars (transportedClosedStalkMap b y' p hy)).obj
            (ModuleCat.of (B.presheaf.stalk y') (B.presheaf.stalk y')))) :=
  (torCongr (quotientIsoTransportedClosedStalk a x' p hx)
    (quotientIsoTransportedClosedStalk b y' p hy) n).toLinearEquiv.length_eq

private theorem isZero_iff_length_eq_zero {Ring : Type u} [CommRing Ring] (L : ModuleCat.{u} Ring) :
    IsZero L ↔ Module.length Ring L = 0 :=
  ModuleCat.isZero_iff_subsingleton.trans Module.length_eq_zero_iff.symm

local notation "I" => integralComponentAt (pullback.fst f g w)
local notation "J" => integralComponentAt (pullback.snd f g w)
set_option quotPrecheck false in
local notation "T" => pullback (C := Scheme) ((I).subschemeι ≫ f) ((J).subschemeι ≫ g)
set_option quotPrecheck false in
local notation "b₀" => Scheme.Hom.productClosedMap f g (I).subschemeι (J).subschemeι

omit [PerfectField k] [IsClosedImmersion p] [IsClosedImmersion q] in
private theorem structureTorCoefficient_congr_product_weighted
    (η : genericPoints T) (hη : b₀ η.val = w)
    (hfinite : Module.length ((T).presheaf.stalk η.val) ((T).presheaf.stalk η.val) ≠ ⊤)
    (h₁ : pullback.fst f g w = p x) (h₂ : pullback.snd f g w = q y)
    (hfin₁ : ∀ n, IsFiniteLength P₀ (((Tor (ModuleCat P₀) n).obj M).obj M'))
    (hfin₂ : ∀ n, IsFiniteLength Q₀ (((Tor (ModuleCat Q₀) n).obj N).obj N'))
    (hsupp₁ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat P₀) n).obj M).obj M')}.Finite)
    (hsupp₂ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat Q₀) n).obj N).obj N')}.Finite) :
    structureTorCoefficient α₀ β₀ =
      structureTorCoefficient α α' * structureTorCoefficient β β' *
        ((Module.length ((T).presheaf.stalk η.val) ((T).presheaf.stalk η.val)).toNat : ℤ) := by
  let x₀ := pullback.fst f g w
  let y₀ := pullback.snd f g w
  have hx : x₀ = p x := h₁
  have hy : y₀ = q y := h₂
  let A₀ := X.presheaf.stalk x₀
  let B₀ := Y.presheaf.stalk y₀
  let : Algebra k A₀ := stalkAlgebraOfField f x₀
  let : Algebra k B₀ := stalkAlgebraOfField g y₀
  obtain ⟨φ, hleft, hright, L, hL⟩ := pullback_stalk_isLocalization_overField f g w
  let : Algebra (A₀ ⊗[k] B₀) R₀ := φ.toAlgebra
  let : IsLocalization L R₀ := hL
  let : Module.Flat (A₀ ⊗[k] B₀) R₀ := IsLocalization.flat R₀ L
  let F := ModuleCat.extendScalars φ
  let M₁ := ModuleCat.of A₀ (A₀ ⧸ IdealSheafData.stalk a.ker x₀)
  let N₁ := ModuleCat.of B₀ (B₀ ⧸ IdealSheafData.stalk b.ker y₀)
  let M₂ := ModuleCat.of A₀ (A₀ ⧸ IdealSheafData.stalk c.ker x₀)
  let N₂ := ModuleCat.of B₀ (B₀ ⧸ IdealSheafData.stalk d.ker y₀)
  have hlenA (n : ℕ) : Module.length A₀ (((Tor (ModuleCat A₀) n).obj M₁).obj M₂) =
      Module.length P₀ (((Tor (ModuleCat P₀) n).obj M).obj M') := by
    let L (w' : X) := ModuleCat.of (X.presheaf.stalk w')
      (X.presheaf.stalk w' ⧸ IdealSheafData.stalk a.ker w')
    let K (w' : X) := ModuleCat.of (X.presheaf.stalk w')
      (X.presheaf.stalk w' ⧸ IdealSheafData.stalk c.ker w')
    exact (congrArg (fun w' : X => Module.length (X.presheaf.stalk w')
      (((Tor (ModuleCat (X.presheaf.stalk w')) n).obj (L w')).obj (K w'))) hx).trans
        (length_quotientTor_eq_length_closedStalks a c (p x) (u x) (u' x) _ _ n)
  have hlenB (n : ℕ) : Module.length B₀ (((Tor (ModuleCat B₀) n).obj N₁).obj N₂) =
      Module.length Q₀ (((Tor (ModuleCat Q₀) n).obj N).obj N') := by
    let L (w' : Y) := ModuleCat.of (Y.presheaf.stalk w')
      (Y.presheaf.stalk w' ⧸ IdealSheafData.stalk b.ker w')
    let K (w' : Y) := ModuleCat.of (Y.presheaf.stalk w')
      (Y.presheaf.stalk w' ⧸ IdealSheafData.stalk d.ker w')
    exact (congrArg (fun w' : Y => Module.length (Y.presheaf.stalk w')
      (((Tor (ModuleCat (Y.presheaf.stalk w')) n).obj (L w')).obj (K w'))) hy).trans
        (length_quotientTor_eq_length_closedStalks b d (q y) (v y) (v' y) _ _ n)
  have hfinA : ∀ n, IsFiniteLength A₀ (((Tor (ModuleCat A₀) n).obj M₁).obj M₂) := by
    intro n
    exact Module.length_ne_top_iff.mp
      (fun htop => (Module.length_ne_top_iff.mpr (hfin₁ n)) ((hlenA n).symm.trans htop))
  have hfinB : ∀ n, IsFiniteLength B₀ (((Tor (ModuleCat B₀) n).obj N₁).obj N₂) := by
    intro n
    exact Module.length_ne_top_iff.mp
      (fun htop => (Module.length_ne_top_iff.mpr (hfin₂ n)) ((hlenB n).symm.trans htop))
  have hsuppA : {n : ℕ | ¬ IsZero (((Tor (ModuleCat A₀) n).obj M₁).obj M₂)}.Finite := by
    refine hsupp₁.subset fun n hn hz => hn ?_
    exact (isZero_iff_length_eq_zero _).mpr
      ((hlenA n).trans ((isZero_iff_length_eq_zero _).mp hz))
  have hsuppB : {n : ℕ | ¬ IsZero (((Tor (ModuleCat B₀) n).obj N₁).obj N₂)}.Finite := by
    refine hsupp₂.subset fun n hn hz => hn ?_
    exact (isZero_iff_length_eq_zero _).mpr
      ((hlenB n).trans ((isZero_iff_length_eq_zero _).mp hz))
  have hres := length_extendExteriorResidueTensor_eq_length_stalk
    f g p q z φ hleft hright η hη
  obtain ⟨_, _, h⟩ := ModuleCat.Tor.finsum_length_extendScalars_exteriorTensor
    (k := k) (S := R₀) M₁ M₂ N₁ N₂ hfinA hfinB hsuppA hsuppB (by
      exact hres.trans_ne hfinite)
  change (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ((Module.length R₀
      (((Tor (ModuleCat R₀) n).obj (F.obj (ModuleCat.exteriorTensorObj k M₁ N₁))).obj
        (F.obj (ModuleCat.exteriorTensorObj k M₂ N₂)))).toNat : ℤ)) =
    ((∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length A₀ (((Tor (ModuleCat A₀) n).obj M₁).obj M₂)).toNat : ℤ)) *
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length B₀ (((Tor (ModuleCat B₀) n).obj N₁).obj N₂)).toNat : ℤ))) *
    ((Module.length R₀ (F.obj (ModuleCat.exteriorTensorObj k
      (ModuleCat.of A₀ (IsLocalRing.ResidueField A₀))
      (ModuleCat.of B₀ (IsLocalRing.ResidueField B₀))))).toNat : ℤ) at h
  rw [hres] at h
  let e₁ := exteriorQuotientsIsoTransportedClosedMapProductStalk f g a b w φ hleft hright
    (r z.val) (productIntersectionMap_point_eq f g a b p q u v hu hv z)
  let e₂ := exteriorQuotientsIsoTransportedClosedMapProductStalk f g c d w φ hleft hright
    (r' z.val) (productIntersectionMap_point_eq f g c d p q u' v' hu' hv' z)
  have h₀' :
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ((Module.length R₀
        (((Tor (ModuleCat R₀) n).obj (F.obj (ModuleCat.exteriorTensorObj k M₁ N₁))).obj
          (F.obj (ModuleCat.exteriorTensorObj k M₂ N₂)))).toNat : ℤ)) =
        structureTorCoefficient α₀ β₀ := by
    unfold structureTorCoefficient
    refine finsum_congr fun n => ?_
    rw [(torCongr e₁ e₂ n).toLinearEquiv.length_eq]
  have hA' :
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length A₀ (((Tor (ModuleCat A₀) n).obj M₁).obj M₂)).toNat : ℤ)) =
          structureTorCoefficient α α' := by
    unfold structureTorCoefficient
    exact finsum_congr fun n => by rw [hlenA n]
  have hB' :
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length B₀ (((Tor (ModuleCat B₀) n).obj N₁).obj N₂)).toNat : ℤ)) =
          structureTorCoefficient β β' := by
    unfold structureTorCoefficient
    exact finsum_congr fun n => by rw [hlenB n]
  rw [h₀', hA', hB'] at h
  exact h

omit [PerfectField k] [IsClosedImmersion p] [IsClosedImmersion q] in
/-- Over an arbitrary field, the product Tor coefficient retains the full generic
multiplicity of the product of the reduced point closures. -/
theorem structureTorCoefficient_product_weighted
    (η : genericPoints T) (hη : b₀ η.val = w)
    (hfinite : Module.length ((T).presheaf.stalk η.val) ((T).presheaf.stalk η.val) ≠ ⊤)
    (hfin₁ : ∀ n, IsFiniteLength P₀ (((Tor (ModuleCat P₀) n).obj M).obj M'))
    (hfin₂ : ∀ n, IsFiniteLength Q₀ (((Tor (ModuleCat Q₀) n).obj N).obj N'))
    (hsupp₁ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat P₀) n).obj M).obj M')}.Finite)
    (hsupp₂ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat Q₀) n).obj N).obj N')}.Finite) :
    structureTorCoefficient α₀ β₀ =
      structureTorCoefficient α α' * structureTorCoefficient β β' *
        ((Module.length ((T).presheaf.stalk η.val) ((T).presheaf.stalk η.val)).toNat : ℤ) :=
  structureTorCoefficient_congr_product_weighted f g a b c d p q u v u' v' hu hv hu' hv' z
    η hη hfinite (productClosedMap_fst_apply f g p q z) (productClosedMap_snd_apply f g p q z)
    hfin₁ hfin₂ hsupp₁ hsupp₂

omit [PerfectField k] in
/-- On a locally Noetherian product of point closures, generic stalks have finite
length automatically. This geometric form has no separate multiplicity finiteness assumption. -/
theorem structureTorCoefficient_product_weighted_of_isLocallyNoetherian
    [IsLocallyNoetherian T]
    (η : genericPoints T) (hη : b₀ η.val = w)
    (hfin₁ : ∀ n, IsFiniteLength P₀ (((Tor (ModuleCat P₀) n).obj M).obj M'))
    (hfin₂ : ∀ n, IsFiniteLength Q₀ (((Tor (ModuleCat Q₀) n).obj N).obj N'))
    (hsupp₁ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat P₀) n).obj M).obj M')}.Finite)
    (hsupp₂ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat Q₀) n).obj N).obj N')}.Finite) :
    structureTorCoefficient α₀ β₀ =
      structureTorCoefficient α α' * structureTorCoefficient β β' *
        ((Module.length ((T).presheaf.stalk η.val) ((T).presheaf.stalk η.val)).toNat : ℤ) := by
  have hdim := ringKrullDim_stalk_eq_zero_of_mem_genericPoints (W := T) η
  let : Ring.KrullDimLE 0 ((T).presheaf.stalk η.val) := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  let : IsArtinianRing ((T).presheaf.stalk η.val) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
  exact structureTorCoefficient_product_weighted f g a b c d p q u v u' v'
    hu hv hu' hv' z η hη
    (show Module.length ((T).presheaf.stalk η.val) ((T).presheaf.stalk η.val) ≠ ⊤ from
      Module.length_ne_top)
    hfin₁ hfin₂ hsupp₁ hsupp₂

/-- The genuine signed Tor coefficient of the product is the product of the two
original signed Tor coefficients at the projected points. -/
theorem structureTorCoefficient_product
    (hfin₁ : ∀ n, IsFiniteLength P₀ (((Tor (ModuleCat P₀) n).obj M).obj M'))
    (hfin₂ : ∀ n, IsFiniteLength Q₀ (((Tor (ModuleCat Q₀) n).obj N).obj N'))
    (hsupp₁ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat P₀) n).obj M).obj M')}.Finite)
    (hsupp₂ : {n : ℕ | ¬ IsZero (((Tor (ModuleCat Q₀) n).obj N).obj N')}.Finite) :
    structureTorCoefficient α₀ β₀ =
      structureTorCoefficient α α' * structureTorCoefficient β β' := by
  obtain ⟨η, hη⟩ := exists_generic_reducedClosures f g p q z
  let : IsIntegral (I).subscheme := isIntegral_integralComponentAt (pullback.fst f g w)
  let : IsIntegral (J).subscheme := isIntegral_integralComponentAt (pullback.snd f g w)
  let : IsReduced T := isReduced_pullback_over_perfectField ((I).subschemeι ≫ f)
    ((J).subschemeι ≫ g)
  let L := (T).presheaf.stalk η.val
  let : Field L := (isField_stalk_of_closure_mem_irreducibleComponents T η.val η.property).toField
  have hlen : Module.length L L = 1 :=
    Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule L L)
  have hfinite : Module.length L L ≠ ⊤ := hlen.trans_ne (by simp)
  have h := structureTorCoefficient_product_weighted f g a b c d p q u v u' v'
    hu hv hu' hv' z η hη hfinite hfin₁ hfin₂ hsupp₁ hsupp₂
  change structureTorCoefficient α₀ β₀ =
    structureTorCoefficient α α' * structureTorCoefficient β β' *
      ((Module.length L L).toNat : ℤ) at h
  simpa only [hlen, ENat.toNat_one, Nat.cast_one, mul_one] using h

end Stacks.Chow
