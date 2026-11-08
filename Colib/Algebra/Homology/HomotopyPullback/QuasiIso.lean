/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.HomotopyPullback.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.CommSq

/-!
Implementation provenance: adapted from the corresponding
`Quillen/Aglib/Algebra/Homology` file at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original homology and weak gluing for homotopy pullbacks

The actual mapping-cocone long exact sequence identifies the original homology
square as a pullback when the preceding difference map is epic. In particular,
either projection is a quasi-isomorphism if the opposite original leg is one.
Both lift-gluing results follow from the strict projection equations and genuine
two-out-of-three. No bounds, projectivity, or abstract homotopy-limit hypothesis
are imposed on the original complexes.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A monic exact biproduct kernel is the actual pullback of the two legs. -/
private theorem isPullback_kernel_biprod {X A B T : C} (k : X ⟶ A ⊞ B) (f : A ⟶ T) (g : B ⟶ T)
    (w : k ≫ biprod.desc f (-g) = 0)
    (hex : (ShortComplex.mk k (biprod.desc f (-g)) w).Exact) [Mono k] :
    IsPullback (k ≫ biprod.fst) (k ≫ biprod.snd) f g := by
  have hk : biprod.lift (k ≫ biprod.fst) (k ≫ biprod.snd) = k := by
    apply biprod.hom_ext <;> simp
  have hw : (k ≫ biprod.fst) ≫ f = (k ≫ biprod.snd) ≫ g := by
    apply sub_eq_zero.mp
    calc
      (k ≫ biprod.fst) ≫ f - (k ≫ biprod.snd) ≫ g =
          biprod.lift (k ≫ biprod.fst) (k ≫ biprod.snd) ≫ biprod.desc f (-g) := by
        simp only [biprod.lift_desc, Preadditive.comp_neg, sub_eq_add_neg]
      _ = 0 := by rw [hk, w]
  let sq : CommSq (k ≫ biprod.fst) (k ≫ biprod.snd) f g := ⟨hw⟩
  have hker : IsLimit sq.kernelFork := by
    simpa only [CommSq.kernelFork, hk] using hex.fIsKernel
  exact IsPullback.of_isLimit (sq.isLimitEquivIsLimitKernelFork.symm hker)

variable {A B T : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T)

/-- A weak second leg makes the original difference map epic on homology. -/
lemma epi_homologyMap_biprod_desc_of_quasiIso [QuasiIso g] (n : ℤ) :
    Epi (homologyMap (biprod.desc f (-g)) n) := by
  have : IsIso (homologyMap (-g) n) := by
    rw [homologyMap_neg]
    exact (-asIso (homologyMap g n)).isIso_hom
  have h : homologyMap (biprod.inr : B ⟶ A ⊞ B) n ≫
      homologyMap (biprod.desc f (-g)) n = homologyMap (-g) n := by
    rw [← homologyMap_comp, biprod.inr_desc]
  exact epi_of_epi_fac h

/-- Surjectivity in the preceding degree makes the actual homology square
of the original mapping-cocone projections a genuine pullback square. -/
lemma homology_homotopyPullback_isPullback (n : ℤ)
    [Epi (homologyMap (biprod.desc f (-g)) (n - 1))] :
    IsPullback (homologyMap (homotopyPullbackFst f g) n)
      (homologyMap (homotopyPullbackSnd f g) n) (homologyMap f n) (homologyMap g n) := by
  let : HasDerivedCategory C := HasDerivedCategory.standard _
  let φ := biprod.desc f (-g)
  let T₀ := CochainComplex.mappingCocone.triangle φ
  have hT := DerivedCategory.mappingCocone_triangle_distinguished φ
  let H := homologyFunctor C (.up ℤ) n
  have hδ : CochainComplex.homologyδOfTriangle T₀ (n - 1) n (by omega) = 0 := by
    apply (cancel_epi (homologyMap φ (n - 1))).mp
    simpa only [comp_zero, T₀, CochainComplex.mappingCocone.triangle_mor₂] using
      CochainComplex.homologyMap_homologyδOfTriangle T₀ hT (n - 1) n (by omega)
  have hmono : Mono (homologyMap T₀.mor₁ n) :=
    (CochainComplex.homologyMap_exact₁_of_distTriang T₀ hT (n - 1) n (by omega)).mono_g hδ
  have hex := CochainComplex.homologyMap_exact₂_of_distTriang T₀ hT n
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBinaryProducts H
  let e := H.mapBiprod A B
  let k := homologyMap T₀.mor₁ n ≫ e.hom
  have he : e.hom ≫ biprod.desc (H.map f) (-H.map g) = H.map φ := by
    simpa only [Functor.map_neg] using biprod.mapBiprod_hom_desc H A B f (-g)
  have w : k ≫ biprod.desc (H.map f) (-H.map g) = 0 := by
    rw [Category.assoc, he]
    exact CochainComplex.homologyMap_comp_eq_zero_of_distTriang T₀ hT n
  have hx : (ShortComplex.mk k (biprod.desc (H.map f) (-H.map g)) w).Exact := by
    apply ShortComplex.exact_of_iso _ hex
    refine ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) ?_ ?_
    · simp [k]
    · simpa only [T₀, H, CochainComplex.mappingCocone.triangle_mor₂,
        CochainComplex.mappingCocone.triangle_obj₂, Iso.refl_hom, Category.comp_id,
        homologyFunctor_map] using he
  have : Mono k := by dsimp [k]; infer_instance
  have hi := isPullback_kernel_biprod k (H.map f) (H.map g) w hx
  have hk : k ≫ biprod.fst = homologyMap (homotopyPullbackFst f g) n := by
    dsimp only [k]
    rw [Category.assoc]
    change H.map T₀.mor₁ ≫ e.hom ≫ biprod.fst = H.map (homotopyPullbackFst f g)
    dsimp only [e]
    rw [Functor.mapBiprod_hom, biprod.lift_fst, ← H.map_comp]
    rfl
  have hk' : k ≫ biprod.snd = homologyMap (homotopyPullbackSnd f g) n := by
    dsimp only [k]
    rw [Category.assoc]
    change H.map T₀.mor₁ ≫ e.hom ≫ biprod.snd = H.map (homotopyPullbackSnd f g)
    dsimp only [e]
    rw [Functor.mapBiprod_hom, biprod.lift_snd, ← H.map_comp]
    rfl
  simpa only [hk, hk', H, homologyFunctor_map] using hi

/-- The actual first mapping-cocone projection is a quasi-isomorphism whenever
the original opposite leg is. -/
lemma quasiIso_homotopyPullbackFst [QuasiIso g] : QuasiIso (homotopyPullbackFst f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := epi_homologyMap_biprod_desc_of_quasiIso f g (n - 1)
  exact (homology_homotopyPullback_isPullback f g n).isIso_fst_of_isIso

/-- The symmetric projection is a quasi-isomorphism when its opposite leg is. -/
lemma quasiIso_homotopyPullbackSnd [QuasiIso f] : QuasiIso (homotopyPullbackSnd f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Epi (homologyMap (biprod.desc f (-g)) (n - 1)) := by
    apply epi_of_epi_fac (show homologyMap (biprod.inl : A ⟶ A ⊞ B) (n - 1) ≫
      homologyMap (biprod.desc f (-g)) (n - 1) = homologyMap f (n - 1) from ?_)
    rw [← homologyMap_comp, biprod.inl_desc]
  exact (homology_homotopyPullback_isPullback f g n).isIso_snd_of_isIso

/-- An original weak leg and weak first component give a weak lifted chain
map by the literal projection equation and actual two-out-of-three. -/
lemma quasiIso_homotopyPullbackLift {M : CochainComplex C ℤ}
    (a : M ⟶ A) (b : M ⟶ B) (h : Homotopy (a ≫ f) (b ≫ g))
    [QuasiIso g] [QuasiIso a] : QuasiIso (homotopyPullbackLift f g a b h) := by
  have := quasiIso_homotopyPullbackFst f g
  have : QuasiIso (homotopyPullbackLift f g a b h ≫ homotopyPullbackFst f g) := by
    rw [homotopyPullbackLift_fst]
    infer_instance
  exact (quasiIso_iff_comp_right (homotopyPullbackLift f g a b h)
    (homotopyPullbackFst f g)).mp inferInstance

/-- Symmetric gluing uses the literal second projection equation. -/
lemma quasiIso_homotopyPullbackLift_of_snd {M : CochainComplex C ℤ}
    (a : M ⟶ A) (b : M ⟶ B) (h : Homotopy (a ≫ f) (b ≫ g))
    [QuasiIso f] [QuasiIso b] : QuasiIso (homotopyPullbackLift f g a b h) := by
  have := quasiIso_homotopyPullbackSnd f g
  have : QuasiIso (homotopyPullbackLift f g a b h ≫ homotopyPullbackSnd f g) := by
    rw [homotopyPullbackLift_snd]
    infer_instance
  exact (quasiIso_iff_comp_right (homotopyPullbackLift f g a b h)
    (homotopyPullbackSnd f g)).mp inferInstance

end CochainComplex
