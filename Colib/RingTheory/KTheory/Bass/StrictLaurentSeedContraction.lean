/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed
public import Colib.KTheory.Waldhausen.Iterated.EndotransformationContractionNaturality
public import Colib.Topology.Prespectrum.RelativeHomotopyLoop
public import Colib.Topology.Prespectrum.DiagramNullHomotopy


/-!
# Whole contraction of an original strict Laurent seed

An actual coefficient-natural Model action whose chosen zero endotransformation
is weak has the prescribed endotransformation contraction. The original
source-leg cone null remains fixed while relative concatenation and actual
backtracking cancellation contract its unchanged seed. The same generic
coordinate identities prove coefficient naturality, retaining contraction time,
source-null time and the output-loop coordinate independently.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory SSet
universe u w
namespace Topology.LoopPrespectrum

private theorem seed_comparison_cast_apply {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    {H K H' K' : Homotopy f g} (hH : H = H') (hK : K = K')
    (e : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (cast e J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst hH
  subst hK
  rfl

private theorem seed_transRefl_eq_reparam {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    (H : Homotopy f g) :
    H.trans (Homotopy.refl g) = H.reparam
      ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s,
        Path.Homotopy.transReflReparamAux_mem_I s⟩, by fun_prop⟩
      (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.Homotopy.trans_refl_reparam (H.path n x)
  rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at hp
  exact DFunLike.congr_fun hp s

section SeedEvaluation
variable {E B E' B' : LoopPrespectrum.{u}}
  {f g h : E ⟶ B} {f' g' h' : E' ⟶ B'}
  {n : ℕ} {x : E.space n} {x' : E'.space n} {p : B.space n → B'.space n}

private theorem seed_track_symm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ s, H'.symm.level n (s, x') = p (H.symm.level n (s, x)) :=
  fun s ↦ hH (unitInterval.symm s)

private theorem seed_comparison_refl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.refl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.refl H).level n (r, (s, x))) := fun _ s ↦ hH s

private theorem seed_comparison_symm_natural
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    {J : H.RelHomotopy K} {J' : H'.RelHomotopy K'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x)))) :
    ∀ r s, J'.symm.level n (r, (s, x')) = p (J.symm.level n (r, (s, x))) :=
  fun r s ↦ hJ (unitInterval.symm r) s

private theorem seed_comparison_trans_natural
    {H K L : Homotopy f g} {H' K' L' : Homotopy f' g'}
    {J : H.RelHomotopy K} {M : K.RelHomotopy L}
    {J' : H'.RelHomotopy K'} {M' : K'.RelHomotopy L'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hM : ∀ r s, M'.level n (r, (s, x')) = p (M.level n (r, (s, x)))) :
    ∀ r s, (J'.trans M').level n (r, (s, x')) =
      p ((J.trans M).level n (r, (s, x))) := by
  intro r s
  change ((J'.level n).trans (M'.level n)) (r, (s, x')) =
    p (((J.level n).trans (M.level n)) (r, (s, x)))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hM _ s

private theorem seed_comparison_hcomp_natural
    {H K : Homotopy f g} {L M : Homotopy g h}
    {H' K' : Homotopy f' g'} {L' M' : Homotopy g' h'}
    {J : H.RelHomotopy K} {N : L.RelHomotopy M}
    {J' : H'.RelHomotopy K'} {N' : L'.RelHomotopy M'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hN : ∀ r s, N'.level n (r, (s, x')) = p (N.level n (r, (s, x)))) :
    ∀ r s, (J'.hcomp N').level n (r, (s, x')) =
      p ((J.hcomp N).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.hcomp
  change (ContinuousMap.Homotopy.trans _ _) (s, (r, x')) =
    p ((ContinuousMap.Homotopy.trans _ _) (s, (r, x)))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact hJ r _
  · exact hN r _

private theorem seed_comparison_transRefl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.transRefl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.transRefl H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.transRefl
  simp only [eq_mp_eq_cast, seed_comparison_cast_apply, seed_transRefl_eq_reparam]
  exact hH _

private theorem seed_comparison_reflTransSymm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflTransSymm H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflTransSymm H).level n (r, (s, x))) := by
  intro r s
  exact hH _

private theorem seed_comparison_reflTrans_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflTrans H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflTrans H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.reflTrans
  simp only [eq_mp_eq_cast, seed_comparison_cast_apply,
    Homotopy.symm_trans, Homotopy.symm_refl, Homotopy.symm_symm]
  exact seed_comparison_transRefl_natural (seed_track_symm_natural hH) r (unitInterval.symm s)

private theorem seed_comparison_reflSymmTrans_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflSymmTrans H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflSymmTrans H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.reflSymmTrans
  simp only [eq_mp_eq_cast, seed_comparison_cast_apply, Homotopy.symm_symm]
  exact seed_comparison_reflTransSymm_natural (seed_track_symm_natural hH) r s

end SeedEvaluation
end Topology.LoopPrespectrum

namespace KTheory.Bass.LaurentSeed
variable {R : CommRingCat.{u}} {C : Under R ⥤ WideSubcategory preservesZero.{w}} (A : ModelAction C)
  (hz : ∀ (a : Under R) (X : (C.obj a).obj.Obj),
    (C.obj ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((zeroEndotransformation (C.map ((laurentUnderCoefficient R).app a))).app X))

/-- The same original unit whiskered along the unchanged Laurent coefficient functor. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:168"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
def ModelAction.pullbackUnitIso (a : Under R) :
    (C.map ((laurentUnderCoefficient R).app a)).hom.toFunctor ≅
      (C.map ((laurentUnderCoefficient R).app a)).hom.toFunctor :=
  onFunctor (C.map ((laurentUnderCoefficient R).app a)).hom.toFunctor (A.unit a)

/-- The original unit hom is weak by its actual isomorphism. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:174"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem ModelAction.pullbackUnit_hom_weak (a : Under R) (X : (C.obj a).obj.Obj) :
    (C.obj ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((A.pullbackUnitIso a).hom.app X) :=
  (C.obj ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq_iso _
    (NatIso.hom_app_isIso (A.pullbackUnitIso a) X)

/-- The existing chosen contraction of the same original forward Laurent action. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:181"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
def ModelAction.contraction (a : Under R) :
    (A.track.homotopy a).RelHomotopy
      (LoopPrespectrum.Homotopy.refl
      ((C ⋙ prespectrumFunctor).map ((laurentUnderCoefficient R).app a))) :=
  prespectrumEndotransformationContraction (C.map ((laurentUnderCoefficient R).app a))
    (A.pullbackUnitIso a).hom (A.pullbackUnit_hom_weak a) (hz a)

attribute [local irreducible] prespectrumEndotransformationContraction

/-- The actual action square keeps both independent contraction and scalar times. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:191"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem ModelAction.contraction_naturality {a b : Under R} (g : a ⟶ b)
    (n : ℕ) (r t : unitInterval) (x : (prespectrum (C.obj a)).space n) :
    ((C ⋙ prespectrumFunctor).map ((laurentUnderFunctor R).map g)).map n
      ((A.contraction hz a).level n (r, (t, x))) =
    (A.contraction hz b).level n
      (r, (t, ((C ⋙ prespectrumFunctor).map g).map n x)) := by
  have h : C.map ((laurentUnderCoefficient R).app a) ≫
      C.map ((laurentUnderFunctor R).map g) =
    C.map g ≫ C.map ((laurentUnderCoefficient R).app b) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg C.map ((laurentUnderCoefficient R).naturality g).symm
  let η := A.pullbackUnitIso a
  let θ := A.pullbackUnitIso b
  have he : Functor.whiskerRight η.hom (C.map ((laurentUnderFunctor R).map g)).hom.toFunctor =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h) ≫
        Functor.whiskerLeft (C.map g).hom.toFunctor θ.hom ≫
          eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h.symm) := by
    apply (cancel_mono (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h))
      (A.unit a) (A.unit b) (A.naturality g).whisker
  exact prespectrumEndotransformationContraction_naturality
    (C.map ((laurentUnderCoefficient R).app a)) (C.map ((laurentUnderCoefficient R).app b))
    (C.map g) (C.map ((laurentUnderFunctor R).map g)) h η.hom θ.hom
    (A.pullbackUnit_hom_weak a) (A.pullbackUnit_hom_weak b) (hz a) (hz b) he n r t x

/-- Conjugate the same whole action contraction by the unchanged source-leg null. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:218"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
def ModelAction.seedNullComparison (a : Under R) :
    (((A.track.homotopy a).postcomp
      (mappingConeInclusion (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) a))))
      |>.conjugateToZero (sourceNull (C ⋙ prespectrumFunctor) a)).RelHomotopy
      (LoopPrespectrum.Homotopy.refl
        (zeroHom (prespectrum (C.obj a)) (cone (C ⋙ prespectrumFunctor) a))) := by
  let N := sourceNull (C ⋙ prespectrumFunctor) a
  let J := (A.contraction hz a).postcomp
    (mappingConeInclusion (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) a)))
  exact ((LoopPrespectrum.Homotopy.RelHomotopy.refl N.symm).hcomp
    ((J.hcomp (LoopPrespectrum.Homotopy.RelHomotopy.refl N)).trans
      (LoopPrespectrum.Homotopy.RelHomotopy.reflTrans N))).trans
        (LoopPrespectrum.Homotopy.RelHomotopy.reflSymmTrans N).symm

/-- Currying the same prescribed joint family nulls the original seed map. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:233"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
def ModelAction.seedNullHomotopy (a : Under R) :
    LoopPrespectrum.Homotopy (A.track.seedMap a)
      (zeroHom (prespectrum (C.obj a)) (parameterLooping (cone (C ⋙ prespectrumFunctor) a))) :=
  (A.seedNullComparison hz a).zeroLoopMapHomotopy

/-- Every original coefficient map keeps the actual joint seed-null family. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:239"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem ModelAction.seedNullComparison_naturality {a b : Under R} (g : a ⟶ b)
    (n : ℕ) (r t : unitInterval) (x : (prespectrum (C.obj a)).space n) :
    (coefficientConeMap (C ⋙ prespectrumFunctor) g).map n
      ((A.seedNullComparison hz a).level n (r, (t, x))) =
    (A.seedNullComparison hz b).level n
      (r, (t, ((C ⋙ prespectrumFunctor).map g).map n x)) := by
  have hN : ∀ s, (sourceNull (C ⋙ prespectrumFunctor) b).level n
      (s, ((C ⋙ prespectrumFunctor).map g).map n x) =
    (coefficientConeMap (C ⋙ prespectrumFunctor) g).map n
      ((sourceNull (C ⋙ prespectrumFunctor) a).level n (s, x)) :=
    fun s ↦ (sourceNull_coefficient (C ⋙ prespectrumFunctor) g n s x).symm
  have hJ : ∀ r t,
      ((A.contraction hz b).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) b)))).level n
        (r, (t, ((C ⋙ prespectrumFunctor).map g).map n x)) =
    (coefficientConeMap (C ⋙ prespectrumFunctor) g).map n
      (((A.contraction hz a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) a)))).level n (r, (t, x))) := by
    intro r t
    change (mappingConeInclusion
      (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) b))).map n
      ((A.contraction hz b).level n
        (r, (t, ((C ⋙ prespectrumFunctor).map g).map n x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) b))).map n
        (((C ⋙ prespectrumFunctor).map ((laurentUnderFunctor R).map g)).map n
          ((A.contraction hz a).level n (r, (t, x))))
    exact congrArg
      ((mappingConeInclusion (StrictSquare.comparison (square (C ⋙ prespectrumFunctor) b))).map n)
      (A.contraction_naturality hz g n r t x).symm
  unfold ModelAction.seedNullComparison
  exact (seed_comparison_trans_natural
    (seed_comparison_hcomp_natural
      (seed_comparison_refl_natural (seed_track_symm_natural hN))
      (seed_comparison_trans_natural
        (seed_comparison_hcomp_natural hJ (seed_comparison_refl_natural hN))
        (seed_comparison_reflTrans_natural hN)))
    (seed_comparison_symm_natural (seed_comparison_reflSymmTrans_natural hN)) r t).symm

/-- The null time and output-loop coordinate remain independent under coefficient change. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:281"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem ModelAction.seedNullHomotopy_naturality {a b : Under R} (g : a ⟶ b)
    (n : ℕ) (r : unitInterval) (x : (prespectrum (C.obj a)).space n) :
    (parameterLoopingMap (coefficientConeMap (C ⋙ prespectrumFunctor) g)).map n
      ((A.seedNullHomotopy hz a).level n (r, x)) =
    (A.seedNullHomotopy hz b).level n
      (r, ((C ⋙ prespectrumFunctor).map g).map n x) := by
  apply Path.ext
  funext t
  exact A.seedNullComparison_naturality hz g n r t x

/-- Bundle the same original seed null with the identity of its actual Bass target. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictLaurentSeedContraction.lean:292"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
def ModelAction.seedDiagramNull :
    DiagramNullHomotopy A.track.seed
      (𝟙 ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (C ⋙ prespectrumFunctor))) where
  homotopy a := (A.seedNullHomotopy hz a).cast (Category.comp_id _).symm rfl
  naturality g n r x := A.seedNullHomotopy_naturality hz g n r x

end KTheory.Bass.LaurentSeed


namespace KTheory.Bass.LaurentSeed.ModelAction

attribute [colib_tag "COL-0587"]
  contraction_naturality

attribute [colib_tag "COL-0587"]
  seedNullComparison

attribute [colib_tag "COL-0587"]
  seedDiagramNull

end KTheory.Bass.LaurentSeed.ModelAction
