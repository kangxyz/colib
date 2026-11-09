/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.StableEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-!
# Actual prespectrum equivalences from zero-preserving exact model equivalences

The original forward functor is retained. Its actual categorical inverse is canonically zero
normalized, and the original unit and counit supply whole coherent inverse homotopies. Every
level, including the zeroth loop level, therefore has an actual homotopy inverse.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence
open SmallWaldhausenCategory Topology
variable {V W : WideSubcategory preservesZero.{u}} (e : V.obj.Obj ≌ W.obj.Obj)
  (hF : IsExact V.obj.waldhausen.cof V.obj.waldhausen.weq
    W.obj.waldhausen.cof W.obj.waldhausen.weq e.functor)
  (hG : IsExact W.obj.waldhausen.cof W.obj.waldhausen.weq
    V.obj.waldhausen.cof V.obj.waldhausen.weq e.inverse)
  (h0 : e.functor.obj V.obj.waldhausen.zero = W.obj.waldhausen.zero)

/-- The original strictly zero-preserving exact functor. -/
def forward : V ⟶ W := ⟨⟨e.functor, hF⟩, h0⟩

/-- The actual inverse functor with its canonical original chosen-zero normalization. -/
def backward : W ⟶ V :=
  ⟨⟨CategoryTheory.rebaseFunctor e.inverse W.obj.waldhausen.zero V.obj.waldhausen.zero
      ((hG.zero W.obj.waldhausen.isZero).iso V.obj.waldhausen.isZero),
    hG.rebase⟩, CategoryTheory.rebaseFunctor_obj_base _ _ _ _⟩

/-- The original categorical unit, pasted with the actual inverse normalization comparison. -/
def unitIso : (forward e hF h0 ≫ backward e hG).hom.toFunctor ≅ (𝟙 V : V ⟶ V).hom.toFunctor :=
  isoWhiskerLeft e.functor
    (CategoryTheory.rebaseFunctorIso e.inverse W.obj.waldhausen.zero V.obj.waldhausen.zero
      ((hG.zero W.obj.waldhausen.isZero).iso V.obj.waldhausen.isZero)).symm ≪≫ e.unitIso.symm

/-- The original categorical counit, pasted with the same inverse normalization comparison. -/
def counitIso : (backward e hG ≫ forward e hF h0).hom.toFunctor ≅ (𝟙 W : W ⟶ W).hom.toFunctor :=
  isoWhiskerRight
    (CategoryTheory.rebaseFunctorIso e.inverse W.obj.waldhausen.zero V.obj.waldhausen.zero
      ((hG.zero W.obj.waldhausen.isZero).iso V.obj.waldhausen.isZero)).symm e.functor ≪≫ e.counitIso

/-- The actual full prespectrum left inverse comparison. -/
def leftHomotopy :
    LoopPrespectrum.Homotopy
      (prespectrumMap (forward e hF h0) ≫ prespectrumMap (backward e hG))
      (𝟙 (prespectrum V)) :=
  (prespectrumTransformationHomotopy (F := forward e hF h0 ≫ backward e hG) (G := 𝟙 V)
    (unitIso e hF hG h0).hom (fun _ => V.obj.waldhausen.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_id _)

/-- The actual full prespectrum right inverse comparison. -/
def rightHomotopy :
    LoopPrespectrum.Homotopy
      (prespectrumMap (backward e hG) ≫ prespectrumMap (forward e hF h0))
      (𝟙 (prespectrum W)) :=
  (prespectrumTransformationHomotopy (F := backward e hG ≫ forward e hF h0) (G := 𝟙 W)
    (counitIso e hF hG h0).hom (fun _ => W.obj.waldhausen.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_id _)

/-- The unchanged original forward map has an actual homotopy inverse at every level. -/
def levelHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((prespectrum V).space n) ((prespectrum W).space n) where
  toFun := (prespectrumMap (forward e hF h0)).map n
  invFun := (prespectrumMap (backward e hG)).map n
  left_inv := ⟨((leftHomotopy e hF hG h0).levelHomotopy n).toHomotopy⟩
  right_inv := ⟨((rightHomotopy e hF hG h0).levelHomotopy n).toHomotopy⟩

include hG in
/-- The original map is a complete weak equivalence at every actual level. -/
theorem level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((prespectrumMap (forward e hF h0)).map n) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (levelHomotopyEquiv e hF hG h0 n)

include hG in
/-- In particular the original prespectrum map is a genuine stable equivalence. -/
theorem isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence (prespectrumMap (forward e hF h0)) :=
  LoopPrespectrum.isStableEquivalence_of_levelwise _
    (level_isWeakHomotopyEquivalence e hF hG h0)


/-- The full left inverse track retains its at zero equation in every level. -/
theorem leftHomotopy_at_zero (n : ℕ) (x : (prespectrum V).space n) :
    (leftHomotopy e hF hG h0).level n (0, x) =
      (prespectrumMap (backward e hG)).map n ((prespectrumMap (forward e hF h0)).map n x) :=
  (leftHomotopy e hF hG h0).at_zero n x

/-- The full left inverse track retains its at one equation in every level. -/
theorem leftHomotopy_at_one (n : ℕ) (x : (prespectrum V).space n) :
    (leftHomotopy e hF hG h0).level n (1, x) =
      x :=
  (leftHomotopy e hF hG h0).at_one n x

/-- The full left inverse track retains its at point equation in every level. -/
theorem leftHomotopy_at_point (n : ℕ) (s : unitInterval) :
    (leftHomotopy e hF hG h0).level n (s, (prespectrum V).point n) =
      (prespectrum V).point n :=
  (leftHomotopy e hF hG h0).at_point n s

/-- The full left inverse track retains its comm equation in every level. -/
theorem leftHomotopy_comm (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n) :
    (leftHomotopy e hF hG h0).level (n+1) (s, (prespectrum V).structureMap n x t) =
      (prespectrum V).structureMap n ((leftHomotopy e hF hG h0).level n (s, x)) t :=
  (leftHomotopy e hF hG h0).comm n s x t

/-- The full right inverse track retains its at zero equation in every level. -/
theorem rightHomotopy_at_zero (n : ℕ) (x : (prespectrum W).space n) :
    (rightHomotopy e hF hG h0).level n (0, x) =
      (prespectrumMap (forward e hF h0)).map n ((prespectrumMap (backward e hG)).map n x) :=
  (rightHomotopy e hF hG h0).at_zero n x

/-- The full right inverse track retains its at one equation in every level. -/
theorem rightHomotopy_at_one (n : ℕ) (x : (prespectrum W).space n) :
    (rightHomotopy e hF hG h0).level n (1, x) =
      x :=
  (rightHomotopy e hF hG h0).at_one n x

/-- The full right inverse track retains its at point equation in every level. -/
theorem rightHomotopy_at_point (n : ℕ) (s : unitInterval) :
    (rightHomotopy e hF hG h0).level n (s, (prespectrum W).point n) =
      (prespectrum W).point n :=
  (rightHomotopy e hF hG h0).at_point n s

/-- The full right inverse track retains its comm equation in every level. -/
theorem rightHomotopy_comm (n : ℕ) (s t : unitInterval) (x : (prespectrum W).space n) :
    (rightHomotopy e hF hG h0).level (n+1) (s, (prespectrum W).structureMap n x t) =
      (prespectrum W).structureMap n ((rightHomotopy e hF hG h0).level n (s, x)) t :=
  (rightHomotopy e hF hG h0).comm n s x t

end CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence

attribute [colib_tag "COL-0357",
  colib_ref "Waldhausen1985" "Section 1.3, Proposition 1.3.1, pp. 330-331" "background"
    "Actual exact-functor maps and weak-natural-transformation invariance"]
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.leftHomotopy
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.rightHomotopy
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.levelHomotopyEquiv
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.isStableEquivalence
