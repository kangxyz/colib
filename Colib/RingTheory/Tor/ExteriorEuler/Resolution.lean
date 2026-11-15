/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Tor.ExteriorEuler.ScalarExtension
public import Colib.RingTheory.Tor.ExteriorEuler.Total
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.Homology.KFlat.BifunctorSingleBothFactors
public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Homology.Tor.ChangeOfRingsSpectralSequence
public import StacksFrontier.RingTheory.Tor.Balancing.Naturality

/-!
# Exterior tensor resolutions and Tor

The exterior tensor total of two flat resolutions is a flat resolution of their
exterior tensor. After flat scalar extension, tensoring that resolution with the
second exterior coefficient computes actual categorical Tor. The coefficient
comparison uses the ring-linear interchange on the two input tensor products.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

namespace CochainComplex

universe u

variable {k A B S : Type u} [Field k] [CommRing A] [CommRing B] [CommRing S]
  [Algebra k A] [Algebra k B] [Algebra (A ⊗[k] B) S]

local notation "c" => ComplexShape.up ℤ
local notation "T" => A ⊗[k] B
local notation "F" => ModuleCat.exteriorTensor (k := k) (A := A) (B := B)
local notation "E" => (ModuleCat.extendScalars (algebraMap T S) : ModuleCat T ⥤ ModuleCat S)
local notation "box" => ModuleCat.exteriorTensorObj k

private theorem isZero_exteriorDouble_entry
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (L : CochainComplex (ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (p q : ℤ) (h : 0 < p ∨ 0 < q) :
    IsZero (((exteriorDouble (k := k) K L).X p).X q) := by
  rcases h with hp | hq
  · exact ((F).flip.obj (L.X q)).map_isZero (K.isZero_of_isStrictlyLE 0 p hp)
  · exact ((F).obj (K.X p)).map_isZero (L.isZero_of_isStrictlyLE 0 q hq)

private theorem quasiIso_exteriorTotal_left
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (L : CochainComplex (ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] [K'.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ K') [QuasiIso f] : QuasiIso (mapBifunctorMap f (𝟙 L) F c) := by
  unfold mapBifunctorMap
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound_flip _ 0 0
    (isZero_exteriorDouble_entry (k := k) K L) (isZero_exteriorDouble_entry (k := k) K' L) ?_
  intro q
  change QuasiIso ((((F).flip.obj (L.X q)).mapHomologicalComplex c).map f)
  infer_instance

private theorem quasiIso_exteriorTotal_right
    (K : CochainComplex (ModuleCat.{u} A) ℤ) {L L' : CochainComplex (ModuleCat.{u} B) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] [L'.IsStrictlyLE 0]
    (g : L ⟶ L') [QuasiIso g] : QuasiIso (mapBifunctorMap (𝟙 K) g F c) := by
  unfold mapBifunctorMap
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  have hcol (U : CochainComplex (ModuleCat.{u} B) ℤ) [U.IsStrictlyLE 0]
      (p : ℤ) (hp : 0 < p) : IsZero ((exteriorDouble (k := k) K U).X p) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro q
    exact (isZero_exteriorDouble_entry (k := k) K U p q (Or.inl hp)).eq_of_src _ _
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound _ 0 0 (hcol L)
    (fun p q hq => isZero_exteriorDouble_entry (k := k) K L p q (Or.inr hq)) (hcol L')
    (fun p q hq => isZero_exteriorDouble_entry (k := k) K L' p q (Or.inr hq)) ?_
  intro p
  change QuasiIso ((((F).obj (K.X p)).mapHomologicalComplex c).map g)
  infer_instance

variable {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
  [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
  {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}

/-- Exterior tensoring the two augmentations gives a quasi-isomorphism onto the exterior
tensor of the coefficient modules, placed in degree zero. -/
def exteriorResolutionAugmentation (f : K ⟶ (single _ c 0).obj M)
    (g : L ⟶ (single _ c 0).obj N) :
    (exteriorDouble (k := k) K L).total c ⟶ (single _ c 0).obj (box M N) :=
  mapBifunctorMap f (𝟙 L) F c ≫ mapBifunctorMap (𝟙 _) g F c ≫
    (KFlatBifunctor.mapBifunctorSingleBothIso F M N).hom

instance exteriorResolutionAugmentation_quasiIso (f : K ⟶ (single _ c 0).obj M)
    (g : L ⟶ (single _ c 0).obj N) [QuasiIso f] [QuasiIso g] :
    QuasiIso (exteriorResolutionAugmentation (k := k) f g) := by
  have := quasiIso_exteriorTotal_left (k := k) L f
  have := quasiIso_exteriorTotal_right (k := k) ((single _ c 0).obj M) g
  unfold exteriorResolutionAugmentation
  infer_instance

instance exteriorTotal_isStrictlyLE :
    CochainComplex.IsStrictlyLE ((exteriorDouble (k := k) K L).total c) 0 := by
  refine (CochainComplex.isStrictlyLE_iff _ 0).2 fun n hn => ?_
  refine HomologicalComplex₂.isZero_total_X_of_isZero _ c n fun p q hpq => ?_
  change p + q = n at hpq
  exact isZero_exteriorDouble_entry (k := k) K L p q (by omega)

omit [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] in
/-- The exterior total has flat terms when both input complexes do. -/
theorem flat_exteriorTotal_X (hK : ∀ p, Module.Flat A (K.X p))
    (hL : ∀ q, Module.Flat B (L.X q)) (n : ℤ) :
    Module.Flat T (((exteriorDouble (k := k) K L).total c).X n) := by
  let D := exteriorDouble (k := k) K L
  let I : Type := ComplexShape.π c c c ⁻¹' {n}
  let G : I → ModuleCat.{u} T := D.toGradedObject.mapObjFun (ComplexShape.π c c c) n
  let : ∀ pq : I, Module.Flat T (G pq) := fun pq => by
    have := hK pq.1.1
    have := hL pq.1.2
    exact ModuleCat.flat_exteriorTensorObj (k := k) (K.X pq.1.1) (L.X pq.1.2)
  change Module.Flat T (∐ G : ModuleCat.{u} T)
  exact Module.Flat.of_linearEquiv (ModuleCat.coprodIsoDirectSum G).toLinearEquiv

/-- The scalar-extended exterior resolution augments to the scalar-extended exterior module. -/
def exteriorResolutionBaseChangeAugmentation (f : K ⟶ (single _ c 0).obj M)
    (g : L ⟶ (single _ c 0).obj N) :
    exteriorTotalBaseChange (k := k) (S := S) K L ⟶ (single _ c 0).obj ((E).obj (box M N)) :=
  ((E).mapHomologicalComplex c).map (exteriorResolutionAugmentation (k := k) f g) ≫
    (singleMapHomologicalComplex E c 0).hom.app (box M N)

variable [Module.Flat (A ⊗[k] B) S]

instance exteriorResolutionBaseChangeAugmentation_quasiIso (f : K ⟶ (single _ c 0).obj M)
    (g : L ⟶ (single _ c 0).obj N) [QuasiIso f] [QuasiIso g] :
    QuasiIso (exteriorResolutionBaseChangeAugmentation (k := k) (S := S) f g) := by
  let : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat T S))
  unfold exteriorResolutionBaseChangeAugmentation
  infer_instance

omit [Module.Flat (A ⊗[k] B) S] in
/-- The base-changed exterior resolution is K-flat. -/
theorem kFlat_exteriorTotalBaseChange (hK : ∀ p, Module.Flat A (K.X p))
    (hL : ∀ q, Module.Flat B (L.X q)) :
    (exteriorTotalBaseChange (k := k) (S := S) K L).KFlat := by
  let P := exteriorTotalBaseChange (k := k) (S := S) K L
  have : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff P 0).2 fun n hn =>
    (E).map_isZero (CochainComplex.isZero_of_isStrictlyLE
      (show CochainComplex (ModuleCat T) ℤ from (exteriorDouble (k := k) K L).total c) 0 n hn)
  have (n : ℤ) : Module.Flat S (P.X n) := by
    let U := ((exteriorDouble (k := k) K L).total c).X n
    let : Module.Flat T U := flat_exteriorTotal_X (k := k) hK hL n
    let a := algebraMap T S
    let : Algebra T S := a.toAlgebra
    change Module.Flat S (TensorProduct T S U)
    exact Module.Flat.baseChange T S U
  exact CochainComplex.KFlat.kFlat_of_flat P 0

variable (M₀ : ModuleCat.{u} A) (N₀ : ModuleCat.{u} B)

set_option maxHeartbeats 600000 in
-- Comparing the two displayed tensor functors unfolds their bundled module actions.
omit [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] [Module.Flat (A ⊗[k] B) S] in
/-- Tensoring the exterior total by an exterior module applies the coefficient tensor in
each input complex. Both sides have the same total-complex signs. -/
def exteriorTotalTensorLeftIso :
    ((tensorLeft (box M₀ N₀)).mapHomologicalComplex c).obj
        ((exteriorDouble (k := k) K L).total c) ≅
      (exteriorDouble (k := k) (((tensorLeft M₀).mapHomologicalComplex c).obj K)
        (((tensorLeft N₀).mapHomologicalComplex c).obj L)).total c := by
  refine Functor.mapBifunctorTotalIso F F (tensorLeft M₀) (tensorLeft N₀)
    (tensorLeft (box M₀ N₀))
    (fun U V => ModuleCat.exteriorTensorTensorIso (k := k) M₀ U N₀ V) c c c ?_ ?_ K L
  · intro U U' f V
    change (𝟙 (box M₀ N₀) ⊗ₘ ModuleCat.exteriorTensorMap (k := k) f (𝟙 V)) ≫
        (ModuleCat.exteriorTensorTensorIso (k := k) M₀ U' N₀ V).hom =
      (ModuleCat.exteriorTensorTensorIso (k := k) M₀ U N₀ V).hom ≫
        ModuleCat.exteriorTensorMap (k := k) (𝟙 M₀ ⊗ₘ f) (𝟙 (N₀ ⊗ V : ModuleCat B))
    have h := ModuleCat.exteriorTensorTensorIso_hom_naturality (k := k)
      (𝟙 M₀) (𝟙 N₀) f (𝟙 V)
    simpa only [ModuleCat.exteriorTensorMap_id, id_tensorHom, whiskerLeft_id] using h
  · intro U V V' g
    change (𝟙 (box M₀ N₀) ⊗ₘ ModuleCat.exteriorTensorMap (k := k) (𝟙 U) g) ≫
        (ModuleCat.exteriorTensorTensorIso (k := k) M₀ U N₀ V').hom =
      (ModuleCat.exteriorTensorTensorIso (k := k) M₀ U N₀ V).hom ≫
        ModuleCat.exteriorTensorMap (k := k) (𝟙 (M₀ ⊗ U : ModuleCat A)) (𝟙 N₀ ⊗ₘ g)
    have h := ModuleCat.exteriorTensorTensorIso_hom_naturality (k := k)
      (𝟙 M₀) (𝟙 N₀) (𝟙 U) g
    simpa only [ModuleCat.exteriorTensorMap_id, id_tensorHom, whiskerLeft_id] using h

omit [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] [Module.Flat (A ⊗[k] B) S] in
/-- Extension of scalars identifies the tensor by the exterior coefficient with the
base-changed exterior total of the two complexes with coefficients. -/
def exteriorTotalBaseChangeTensorLeftIso :
    ((tensorLeft ((E).obj (box M₀ N₀))).mapHomologicalComplex c).obj
        (exteriorTotalBaseChange (k := k) (S := S) K L) ≅
      exteriorTotalBaseChange (k := k) (S := S)
        (((tensorLeft M₀).mapHomologicalComplex c).obj K)
        (((tensorLeft N₀).mapHomologicalComplex c).obj L) := by
  let V := (exteriorDouble (k := k) K L).total c
  let Φ := tensorLeft (box M₀ N₀)
  let Ψ := tensorLeft ((E).obj (box M₀ N₀))
  let e : E ⋙ Ψ ≅ Φ ⋙ E := NatIso.ofComponents
    (fun X => Functor.Monoidal.μIso E (box M₀ N₀) X) (fun f =>
      Functor.LaxMonoidal.μ_natural_right E (box M₀ N₀) f)
  exact (Functor.mapHomologicalComplexCompIso e c).app V ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Φ ⋙ E)) c).symm.app V ≪≫
    ((E).mapHomologicalComplex c).mapIso
      (exteriorTotalTensorLeftIso (k := k) (K := K) (L := L) M₀ N₀)

/-- The homology of the scalar-extended exterior total with coefficients computes the
actual Tor of the two scalar-extended exterior modules. -/
def exteriorTotalBaseChangeHomologyTorIso
    (f : K ⟶ (single _ c 0).obj M) (g : L ⟶ (single _ c 0).obj N)
    [QuasiIso f] [QuasiIso g] (hK : ∀ p, Module.Flat A (K.X p))
    (hL : ∀ q, Module.Flat B (L.X q)) (n : ℕ) :
    (exteriorTotalBaseChange (k := k) (S := S)
        (((tensorLeft M₀).mapHomologicalComplex c).obj K)
        (((tensorLeft N₀).mapHomologicalComplex c).obj L)).homology (-(n : ℤ)) ≅
      ((CategoryTheory.Tor (ModuleCat.{u} S) n).obj ((E).obj (box M₀ N₀))).obj
        ((E).obj (box M N)) := by
  let P := exteriorTotalBaseChange (k := k) (S := S) K L
  let X := (E).obj (box M₀ N₀)
  let Y := (E).obj (box M N)
  let ε := exteriorResolutionBaseChangeAugmentation (k := k) (S := S) f g
  let H := homologyFunctor (ModuleCat.{u} S) c (-(n : ℤ))
  have hP : P.KFlat := kFlat_exteriorTotalBaseChange (k := k) hK hL
  haveI : QuasiIso ε := exteriorResolutionBaseChangeAugmentation_quasiIso f g
  let eTor := Tor.ChangeOfRingsSpectralSequence.torIsoOfKFlatResolution_natCast ε hP X n
  have eTor' : (((tensorLeft X).mapHomologicalComplex c).obj P).homology (-(n : ℤ)) ≅
      (((Tor.moduleTensorBifunctor S).obj Y).leftDerived n).obj X := by
    change _ ≅ Tor.TorInDegree S (n : ℤ) Y X at eTor
    rwa [Tor.TorInDegree, dite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast] at eTor
  let eY : (Tor.moduleTensorBifunctor S).obj Y ≅ tensorLeft Y :=
    NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      rfl
  let eY' : (((Tor.moduleTensorBifunctor S).obj Y).leftDerived n).obj X ≅
      ((tensorLeft Y).leftDerived n).obj X :=
    { hom := (NatTrans.leftDerived eY.hom n).app X
      inv := (NatTrans.leftDerived eY.inv n).app X
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← NatTrans.leftDerived_comp, eY.hom_inv_id,
          NatTrans.leftDerived_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← NatTrans.leftDerived_comp, eY.inv_hom_id,
          NatTrans.leftDerived_id, NatTrans.id_app] }
  exact H.mapIso (exteriorTotalBaseChangeTensorLeftIso (k := k) (S := S)
    (K := K) (L := L) M₀ N₀).symm ≪≫
    eTor' ≪≫ eY' ≪≫ (((Tor_iso_Tor' S n) ≪≫ (torFlip_iso_Tor' S n).symm).app Y).app X

end CochainComplex
