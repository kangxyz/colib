/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.IntegralAffine
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Image

/-!
# Dense-open detection for the transfer Nisnevich sheafification

Affine local-zero neighborhoods detect sections of a separated HI presheaf.
The unit image has both properties and locally generates its target sheaf.
This gives dense-open detection of that sheaf from the integral-affine
local-zero theorem.

Adapted from `Motivic/Cohomology/A1/Sheafification/DenseDetection.lean`
at motivic@a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Dense-open restriction detects zero in a separated HI presheaf once
local-zero neighborhoods are available on integral affine objects. -/
theorem section_eq_zero_of_dense_open_of_separated
    (hD : IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hsep : Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj P))
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (s : P.sections (Cor.mk X))
    (hs : P.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 := by
  classical
  let Q := (toPresheaf k).obj P
  have hlocal := exists_zero_neighborhood_of_dense_open_of_integralAffineLocalZero
    hD a ha P hP s hs
  choose O hO hx hz using hlocal
  let Y (x : X.left) := SmoothSite.mk ((O x).ι ≫ X.hom)
  let f (x : X.left) : Y x ⟶ X := SmoothSite.homMk (O x).ι rfl
  have hpre : Presieve.ofArrows Y f ∈
      SmoothSite.nisnevichPrecoverage (Spec (.of k)) X := by
    apply (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun x ↦ inferInstanceAs (Etale (O x).ι),
      fun x ↦ ⟨x, ⟨x, hx x⟩, rfl,
        inferInstanceAs (IsIso ((O x).ι.residueFieldMap ⟨x, hx x⟩))⟩⟩
  have hcover : Presheaf.equalizerSieve (F := Q) s 0 ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) X := by
    apply SmoothSite.mem_nisnevichTopology_iff.mpr
    refine ⟨Presieve.ofArrows Y f, hpre, ?_⟩
    rw [Presieve.ofArrows_le_iff]
    intro x
    change P.transfer ((Cor.graphFunctor k).map (f x)) s =
      P.transfer ((Cor.graphFunctor k).map (f x)) 0
    rw [map_zero]
    exact hz x
  exact hsep X (Presheaf.equalizerSieve (F := Q) s 0) hcover s 0 (fun _ _ hf ↦ hf)

/-- A pointwise monic and locally surjective map from a separated HI presheaf
gives dense-open detection for its target sheaf. -/
theorem sheaf_section_eq_zero_of_dense_open_of_separated_local_generation
    (hD : IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hsep : Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj P))
    (G : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (m : (toPresheaf k).obj P ⟶ G.obj)
    [∀ Y, Mono (m.app (op Y))]
    [Presheaf.IsLocallySurjective (SmoothSite.nisnevichTopology (Spec (.of k))) m]
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (s : G.obj.obj (op X))
    (hs : G.obj.map a.op s = 0) : s = 0 := by
  classical
  obtain ⟨R, hR, hRm⟩ := SmoothSite.mem_nisnevichTopology_iff.mp
    (Presheaf.imageSieve_mem (SmoothSite.nisnevichTopology (Spec (.of k))) m s)
  have hcov : Sieve.generate R ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X :=
    Precoverage.generate_mem_toGrothendieck hR
  have hsheaf := ((isSheaf_iff_isSheaf_of_type
    (SmoothSite.nisnevichTopology (Spec (.of k))) _).mp
      ((sheafCompose (SmoothSite.nisnevichTopology (Spec (.of k)))
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property).isSheafFor R hcov
  apply hsheaf.isSeparatedFor.ext
  intro Y f hf
  have : Etale f.left := SmoothSite.etale_of_mem_nisnevichPrecoverage hR hf
  obtain ⟨t, ht⟩ := hRm Y f hf
  let B := SmoothSite.etalePullback a f
  let j : B ⟶ Y := SmoothSite.etalePullbackSnd a f
  let b : B ⟶ A := SmoothSite.etalePullbackFst a f
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left f.left))
  have hjdense : DenseRange j.left := by
    change Dense (Set.range (pullback.snd a.left f.left))
    rw [IsOpenImmersion.range_pullbackSnd]
    exact ha.preimage f.left.isOpenMap
  have hj : j ≫ f = b ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm
  have htzero : P.transfer ((Cor.graphFunctor k).map j) t = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (m.app (op B))).mp inferInstance
    rw [map_zero]
    change m.app (op B) (((toPresheaf k).obj P).map j.op t) = 0
    rw [NatTrans.naturality_apply, ht]
    have he := ConcreteCategory.congr_hom (congrArg (fun g ↦ G.obj.map g.op) hj) s
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero] using he
  have ht0 := section_eq_zero_of_dense_open_of_separated hD P hP hsep j hjdense t htzero
  change G.obj.map f.op s = G.obj.map f.op 0
  rw [map_zero, ← ht, ht0, map_zero]

/-- Dense-open detection for the original transfer-preserving Nisnevich
sheafification follows from the integral-affine local-zero theorem. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/A1/Sheafification/DenseDetection.lean"
  "adaptation" "Dense detection through the actual unit image and local generation"]
theorem nisnevichSheafify_section_eq_zero_of_dense_open_of_integralAffineLocalZero
    (hD : IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left)
    (s : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk X))
    (hs : ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map a) s = 0) :
    s = 0 := by
  let m := (toPresheaf k).map (nisnevichImageι P)
  have (Y : SmoothSite (Spec (.of k))) : Mono (m.app (op Y)) :=
    inferInstanceAs (Mono ((nisnevichImageι P).hom.app (op (Cor.mk Y))))
  exact sheaf_section_eq_zero_of_dense_open_of_separated_local_generation hD
    (nisnevichImage P) (nisnevichImage_isA1Invariant P hP)
    (nisnevichImage_isSeparated P)
    ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)) m a ha s hs

end AlgebraicGeometry.PresheafWithTransfers
