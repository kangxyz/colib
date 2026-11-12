/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.ArbitraryPointLocality
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Refinement
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Points.AutomaticCechKernel

/-!
# Genuine signed lift comparison from matching original Cech germs

The common finite image and controlled boundary are constructed, not supplied.
Actual matching germs on its two designated coordinates make the boundary
transfer vanish by arbitrary-point signed locality. The original point-fiber
cocone then compares the original lift values. No closed-point premise or
positive-coefficient reduction is used.

Sources at motivic@a6805c4a87cdfd7717dd7a94039246a167f15380:
`Motivic/Transfers/Sheaf/Germs/Cech/GermComparison.lean`, blob
`62ebe49ab80f3eeba28d712fc73d14bad4fe72d4`, and
`Motivic/Transfers/Sheaf/Germs/Cech/AutomaticSupport.lean`, blob
`7ddf39a231b42e6c99f735e432e45091c4f20dd8`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y V : SmoothSite (Spec (.of k))}

/-- Matching original germs on designated Cech points kills a genuine signed
kernel transfer, using its constructed common finite support. -/
theorem transfer_germ_eq_zero_of_matching_cech_germs_auto_support
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hzero : α ≫ (Cor.graphFunctor k).map q = 0)
    (x : X.left) (T : Set V.left)
    (hfirst : finiteCorrespondences.TargetsIn α x T)
    (hres : ∀ v ∈ T, IsIso (q.left.residueFieldMap v))
    (s : P.sections (Cor.mk V))
    (hcompat : ∀ w : (SmoothSite.etalePullback q q).left,
      (SmoothSite.etalePullbackFst q q).left w ∈ T →
      (SmoothSite.etalePullbackSnd q q).left w ∈ T →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s) =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s)) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) = 0 := by
  obtain ⟨N, β, hβ, hpoint⟩ :=
    Cor.exists_pointed_cech_boundary_with_target_control k α q hzero x T hfirst hres
  let d := ((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s -
    ((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s
  have hd : ∀ b, β.val b ≠ 0 → ∀ z : (integralComponentAt b).subscheme,
      ((integralComponentAt b).subschemeι ≫
        pullback.fst ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom
          (SmoothSite.etalePullback q q).hom) z = N.center →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q)
        (((integralComponentAt b).subschemeι ≫
          pullback.snd ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom
            (SmoothSite.etalePullback q q).hom) z) d = 0 := by
    intro b hb z hz
    obtain ⟨hfst, hsnd⟩ := hpoint b hb z hz
    dsimp only [d]
    rw [map_sub, hcompat _ hfst hsnd, sub_self]
  have hz := transfer_germ_eq_zero_at_point k P β N.center d hd
  have he : ((toPresheaf k).obj P).map N.toBase.op (P.transfer α s) = P.transfer β d := by
    let U := Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N)
    let W := Cor.mk (SmoothSite.etalePullback q q)
    let g : U ⟶ Cor.mk X := (Cor.graphFunctor k).map N.toBase
    let a : W ⟶ Cor.mk V := (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)
    let b : W ⟶ Cor.mk V := (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)
    have h : g ≫ α = β ≫ a - β ≫ b := hβ
    change (P.transfer α ≫ P.transfer g) s = _
    calc
      _ = P.transfer (g ≫ α) s := ConcreteCategory.congr_hom (transfer_comp P g α).symm s
      _ = P.transfer (β ≫ a - β ≫ b) s := congrArg (fun t => P.transfer t s) h
      _ = P.transfer (β ≫ a) s - P.transfer (β ≫ b) s :=
        ConcreteCategory.congr_hom (transfer_sub P (β ≫ a) (β ≫ b)) s
      _ = P.transfer β (P.transfer a s) - P.transfer β (P.transfer b s) :=
        congrArg₂ (· - ·) (ConcreteCategory.congr_hom (transfer_comp P β a) s)
          (ConcreteCategory.congr_hom (transfer_comp P β b) s)
      _ = P.transfer β d := (map_sub (P.transfer β).hom _ _).symm
  have h := ConcreteCategory.congr_hom
    (SmoothSite.restriction_sectionToNisnevichPoint ((toPresheaf k).obj P) N) (P.transfer α s)
  change ((SmoothSite.nisnevichPointFiberCocone X x ((toPresheaf k).obj P)).ι.app (op N))
      (((toPresheaf k).obj P).map N.toBase.op (P.transfer α s)) = _ at h
  exact h.symm.trans ((congrArg _ he).trans
    (SmoothSite.nisnevichPointFiberCocone_eq_zero_of_center_germ_eq_zero _ N _ hz))

/-- Equal actual graph images compare on matching representative germs, with
no common support or Cech boundary hypothesis left to the caller. -/
theorem transfer_germ_eq_of_matching_cech_germs_auto_support
    (α α' : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (heq : α ≫ (Cor.graphFunctor k).map q = α' ≫ (Cor.graphFunctor k).map q)
    (x : X.left) (T : Set V.left)
    (hfirst : finiteCorrespondences.TargetsIn α x T)
    (hfirst' : finiteCorrespondences.TargetsIn α' x T)
    (hres : ∀ v ∈ T, IsIso (q.left.residueFieldMap v))
    (s : P.sections (Cor.mk V))
    (hcompat : ∀ w : (SmoothSite.etalePullback q q).left,
      (SmoothSite.etalePullbackFst q q).left w ∈ T →
      (SmoothSite.etalePullbackSnd q q).left w ∈ T →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s) =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s)) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α' s) := by
  have hzero : (α - α') ≫ (Cor.graphFunctor k).map q = 0 := by
    let g : Cor.mk V ⟶ Cor.mk Y := (Cor.graphFunctor k).map q
    change (α - α') ≫ g = 0
    have hg : α ≫ g = α' ≫ g := heq
    rw [Preadditive.sub_comp, hg, sub_self]
  have hdiff : finiteCorrespondences.TargetsIn (α - α') x T := by
    simpa only [sub_eq_add_neg] using hfirst.add hfirst'.neg
  have hz := transfer_germ_eq_zero_of_matching_cech_germs_auto_support k P (α - α') q hzero
    x T hdiff hres s hcompat
  let ι := SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x
  have h : P.transfer (α - α') s = P.transfer α s - P.transfer α' s :=
    ConcreteCategory.congr_hom (transfer_sub P α α') s
  have h' := map_sub ι.hom (P.transfer α s) (P.transfer α' s)
  exact sub_eq_zero.mp (h'.symm.trans ((congrArg ι.hom h.symm).trans hz))

end AlgebraicGeometry.PresheafWithTransfers
