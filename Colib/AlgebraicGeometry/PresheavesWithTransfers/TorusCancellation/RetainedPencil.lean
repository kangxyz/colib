/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.QuadraticCylinder
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.PolynomialFaceProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.RetainSourceEndpoint
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality

/-!
# Flat pullback of the actual quadratic pencil with a retained target coordinate

The monic quotient is pulled back along the original flat source map.
Its paired ambient map is the closed graph fiber. Retaining any original
source coordinate commutes with the literal affine endpoints on that
finite-flat support. Thus the endpoint graph sums survive this operation
over any smooth retained factor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NativeTorusPolynomial Polynomial
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  [IsNoetherianRing R] [IsDomain R]
  {U' X : SmoothSite (Spec (CommRingCat.of k))}

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "U" => affineSite k R
local notation "V" => lineSite (k := k) (R := R)
set_option quotPrecheck false in
local notation "A(" T ")" => affineLineCylinder.obj T
local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)
local notation "σ(" T "," a ")" => nativeAffineSection (CommRingCat.of k) T a
set_option quotPrecheck false in
local notation "point(" a ")" =>
  SmoothSite.homMk (X := U) (Y := Gₖ)
    (nativeAffineTorusPoint (U).hom a).left (affineUnitPoint_over (U).hom a)

private theorem affineLineCylinder_map_flat
    {S : Scheme.{u}} {Y Z : SmoothSite S} (j : Y ⟶ Z) [Flat j.left] :
    Flat (affineLineCylinder.map j).left := by
  exact Flat.isStableUnderBaseChange.of_isPullback
    (productMap_left_isPullback j (additiveGroupObject S)).flip (inferInstance : Flat j.left)

/-- The whole quadratic family after flat pullback and retention of an original source map. -/
def retainedUnitProductCylinderCycle (j : U' ⟶ U) (r : A(U') ⟶ X) (a b : Rˣ) :
    Cor.mk (A(U')) ⟶ Cor.mk (SmoothSite.product X Gₖ) :=
  retainSourceGraph r (γ (affineLineCylinder.map j) ≫ unitProductCylinderCycle (k := k) a b)

private structure ClosedSpanPresentation
    {P Q : SmoothSite (Spec (CommRingCat.of k))} (c : Cor.mk P ⟶ Cor.mk Q) where
  support : Scheme.{u}
  p : support ⟶ P.left
  q : support ⟶ Q.left
  base_eq : p ≫ P.hom = q ≫ Q.hom
  finite_p : IsFinite p
  flat_p : Flat p
  closed : IsClosedImmersion (pullback.lift p q base_eq)
  value_eq : letI := finite_p
    letI := flat_p
    c = ofFiniteFlatSpan p q base_eq

set_option maxHeartbeats 800000 in
-- The native polynomial cycle and the flat graph fiber have dependent span types.
private theorem quadraticPullbackPresentation (j : U' ⟶ U) [Flat j.left] (a b : Rˣ) :
    Nonempty (ClosedSpanPresentation
      (γ (affineLineCylinder.map j) ≫ unitProductCylinderCycle (k := k) a b)) := by
  let e := lineCylinderIso (k := k) (R := R)
  let φ := affineLineCylinder.map j ≫ e.inv
  let : Flat (affineLineCylinder.map j).left := affineLineCylinder_map_flat j
  let : IsIso e.inv.left := inferInstanceAs
    (IsIso ((SmoothSite.forgetScheme Sₖ).mapIso e).inv)
  let : Flat φ.left :=
    inferInstanceAs (Flat ((affineLineCylinder.map j).left ≫ e.inv.left))
  let p := unitProductPencil a b
  let h₀ := unitProductPencil_constant_isUnit a b
  let m : Spec (.of (AdjoinRoot p)) ⟶ pullback (C := Scheme) (V).hom (Gₖ).hom :=
    NativeTorusPolynomial.inclusion (V).hom p h₀
  let p₀ := m ≫ pullback.fst (V).hom (Gₖ).hom
  let q₀ := m ≫ pullback.snd (V).hom (Gₖ).hom
  have hbase : p₀ ≫ (V).hom = q₀ ≫ (Gₖ).hom := by
    simp only [p₀, q₀, Category.assoc, pullback.condition]
  let : IsClosedImmersion m := inclusion_isClosedImmersion (V).hom p h₀
  have hp₀ : p₀ = NativeTorusPolynomial.projection p := inclusion_fst (V).hom p h₀
  let : IsFinite p₀ := hp₀.symm ▸ projection_isFinite p (unitProductPencil_monic a b)
  let : Flat p₀ := hp₀.symm ▸ projection_flat p (unitProductPencil_monic a b)
  have hcycle : (unitProductPencilCycle (V).hom a b : Cor.mk V ⟶ Cor.mk Gₖ) =
      ofFiniteFlatSpan (X := V) (Y := Gₖ) p₀ q₀ hbase :=
    (ofFiniteFlatSpan_pair (Y := V) (Z := Gₖ) m).symm
  let p₁ := pullback.fst φ.left p₀
  let q₁ := pullback.snd φ.left p₀ ≫ q₀
  let h₁ := flatWholeSpan_base φ p₀ q₀ hbase
  have hpre : γ φ ≫ ofFiniteFlatSpan (X := V) (Y := Gₖ) p₀ q₀ hbase =
      ofFiniteFlatSpan (X := A(U')) (Y := Gₖ) p₁ q₁ h₁ :=
    graph_comp_ofFiniteFlatSpan_pair_of_flat (X := A(U')) (Y := V) (Z := Gₖ) φ m
  have hcomp : γ (affineLineCylinder.map j) ≫ γ e.inv = γ φ :=
    ((graphFunctor k).map_comp (affineLineCylinder.map j) e.inv).symm
  have hφ : γ (affineLineCylinder.map j) ≫ unitProductCylinderCycle (k := k) a b =
      ofFiniteFlatSpan (X := A(U')) (Y := Gₖ) p₁ q₁ h₁ := by
    calc
      _ = (γ (affineLineCylinder.map j) ≫ γ e.inv) ≫
          (unitProductPencilCycle (V).hom a b : Cor.mk V ⟶ Cor.mk Gₖ) :=
        (Category.assoc _ _ _).symm
      _ = γ φ ≫ ofFiniteFlatSpan (X := V) (Y := Gₖ) p₀ q₀ hbase :=
        congrArg₂ (fun (f : Cor.mk (A(U')) ⟶ Cor.mk V) (g : Cor.mk V ⟶ Cor.mk Gₖ) => f ≫ g)
          hcomp hcycle
      _ = _ := hpre
  let m' := closedSupportGraphFiberMap (A(U')).hom (V).hom (Gₖ).hom m
    φ.left (MorphismProperty.Over.w φ)
  have he : pullback.lift p₁ q₁ h₁ = m' := by
    apply pullback.hom_ext
    · simp only [p₁, p₀, m', pullback.lift_fst, closedSupportGraphFiberMap_fst]
    · simp only [q₁, p₀, q₀, m', pullback.lift_snd, closedSupportGraphFiberMap_snd]
  have hc : IsClosedImmersion (pullback.lift p₁ q₁ h₁) :=
    he.symm ▸ inferInstanceAs (IsClosedImmersion m')
  exact ⟨⟨_, p₁, q₁, h₁, inferInstance, inferInstance, hc, hφ⟩⟩

private theorem nativeSection_comp_retainedUnitProductCylinderCycle
    (j : U' ⟶ U) [Flat j.left] (r : A(U') ⟶ X) (a b : Rˣ) (c : k) :
    γ (σ(U',c)) ≫ retainedUnitProductCylinderCycle j r a b =
      retainSourceGraph (σ(U',c) ≫ r)
        (γ (σ(U',c)) ≫ γ (affineLineCylinder.map j) ≫ unitProductCylinderCycle (k := k) a b) := by
  obtain ⟨P⟩ := quadraticPullbackPresentation j a b
  let := P.finite_p
  let := P.flat_p
  let := P.closed
  unfold retainedUnitProductCylinderCycle
  rw [P.value_eq]
  exact nativeSection_comp_retainSourceGraph c r P.p P.q P.base_eq

/-- Restricting a retained quadratic pencil along a Cartesian face gives the
same pulled pencil with its retained coordinate pushed along the base map. -/
theorem retainedUnitProductCylinderCycle_graph_precomp
    {U'' X' : SmoothSite (Spec (CommRingCat.of k))}
    (g : U'' ⟶ U') (f : X' ⟶ X) (j : U' ⟶ U) [Flat j.left]
    (j' : U'' ⟶ U) [Flat j'.left] (hj : g ≫ j = j')
    (r : A(U') ⟶ X) (r' : A(U'') ⟶ X') (hr : affineLineCylinder.map g ≫ r = r' ≫ f)
    (t : U'.left ⟶ Spec (.of k[X])) [Flat t] (a : k)
    (H : IsPullback g.left U''.hom t (AffineLineFiber.point a)) (u v : Rˣ) :
    γ (affineLineCylinder.map g) ≫ retainedUnitProductCylinderCycle j r u v =
      retainedUnitProductCylinderCycle j' r' u v ≫ γ (SmoothSite.productMap f (𝟙 Gₖ)) := by
  let φ := affineLineCylinder.map g
  let q := pullback.fst U'.hom (additiveGroupObject Sₖ).hom ≫ t
  let : Flat q := inferInstanceAs
    (Flat (pullback.fst U'.hom (additiveGroupObject Sₖ).hom ≫ t))
  have H' : IsPullback φ.left (A(U'')).hom q (AffineLineFiber.point a) :=
    productMap_cartesian_polynomial_face g (additiveGroupObject Sₖ) t a H
  let β := γ (affineLineCylinder.map j) ≫ unitProductCylinderCycle (k := k) u v
  let β' := γ (affineLineCylinder.map j') ≫ unitProductCylinderCycle (k := k) u v
  have hβ : γ φ ≫ β = β' := by
    change γ (affineLineCylinder.map g) ≫ γ (affineLineCylinder.map j) ≫
      unitProductCylinderCycle (k := k) u v =
        γ (affineLineCylinder.map j') ≫ unitProductCylinderCycle (k := k) u v
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hj]
  obtain ⟨P⟩ := quadraticPullbackPresentation j u v
  obtain ⟨P'⟩ := quadraticPullbackPresentation j' u v
  let := P.finite_p
  let := P.flat_p
  let := P.closed
  let := P'.finite_p
  let := P'.flat_p
  change γ φ ≫ retainSourceGraph r β =
    retainSourceGraph r' β' ≫ γ (SmoothSite.productMap f (𝟙 Gₖ))
  calc
    _ = retainSourceGraph (φ ≫ r) (γ φ ≫ β) := by
      rw [show β = _ from P.value_eq]
      exact graph_comp_retainSourceGraph_of_cartesian_endpoint φ q a H' r P.p P.q P.base_eq
    _ = retainSourceGraph (r' ≫ f) β' := by rw [hr, hβ]
    _ = _ := by
      rw [show β' = _ from P'.value_eq]
      exact (retainSourceGraph_comp_productMap_ofFiniteFlatSpan r' f P'.p P'.q P'.base_eq).symm

private theorem nativeSection_comp_retainedUnitProductCylinderCycle_of_sum
    (j : U' ⟶ U) [Flat j.left] (r : A(U') ⟶ X) (a b u v : Rˣ) (c : k)
    (h : γ (σ(U,c)) ≫ unitProductCylinderCycle (k := k) a b = γ (point(u)) + γ (point(v))) :
    γ (σ(U',c)) ≫ retainedUnitProductCylinderCycle j r a b =
      γ (SmoothSite.productLift (σ(U',c) ≫ r) (j ≫ point(u))) +
        γ (SmoothSite.productLift (σ(U',c) ≫ r) (j ≫ point(v))) := by
  rw [nativeSection_comp_retainedUnitProductCylinderCycle, ← Category.assoc,
    ← Functor.map_comp, nativeAffineSection_naturality, Functor.map_comp, Category.assoc, h]
  simp only [Preadditive.comp_add, map_add, ← Functor.map_comp, retainSourceGraph_graph]

variable [IsIntegrallyClosed R]

/-- The actual zero endpoint retains the source map and gives the product and unit graphs. -/
theorem nativeSection_zero_comp_retainedUnitProductCylinderCycle
    (j : U' ⟶ U) [Flat j.left] (r : A(U') ⟶ X) (a b : Rˣ) :
    γ (σ(U',0)) ≫ retainedUnitProductCylinderCycle j r a b =
      γ (SmoothSite.productLift (σ(U',0) ≫ r) (j ≫ point(a * b))) +
        γ (SmoothSite.productLift (σ(U',0) ≫ r) (j ≫ point(1))) :=
  nativeSection_comp_retainedUnitProductCylinderCycle_of_sum j r a b (a * b) 1 0
    (graph_zero_comp_unitProductCylinderCycle (k := k) a b)

/-- The actual one endpoint retains the source map and gives the two input unit graphs. -/
theorem nativeSection_one_comp_retainedUnitProductCylinderCycle
    (j : U' ⟶ U) [Flat j.left] (r : A(U') ⟶ X) (a b : Rˣ) :
    γ (σ(U',1)) ≫ retainedUnitProductCylinderCycle j r a b =
      γ (SmoothSite.productLift (σ(U',1) ≫ r) (j ≫ point(a))) +
        γ (SmoothSite.productLift (σ(U',1) ≫ r) (j ≫ point(b))) :=
  nativeSection_comp_retainedUnitProductCylinderCycle_of_sum j r a b a b 1
    (graph_one_comp_unitProductCylinderCycle (k := k) a b)

end AlgebraicGeometry.Cor
