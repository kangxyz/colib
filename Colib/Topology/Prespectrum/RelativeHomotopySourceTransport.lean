/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Whole relative homotopies under equality of source and target presentations

Equality elimination retains the complete level maps and the independent structure
coordinate. Endpoint arrows and homotopies are the supplied actual data, not new models.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u

namespace Topology.LoopPrespectrum

/-- Concatenation respects both object presentations and both complete input tracks. -/
theorem Homotopy.trans_level_congr_objects
    {D D' E E' : LoopPrespectrum.{u}} (eD : D = D') (eE : E = E')
    {a b c : D ⟶ E} {a' b' c' : D' ⟶ E'}
    (H : Homotopy a b) (K : Homotopy b c)
    (H' : Homotopy a' b') (K' : Homotopy b' c') (n : ℕ)
    (hH : HEq (H.level n) (H'.level n)) (hK : HEq (K.level n) (K'.level n)) :
    HEq ((H.trans K).level n) ((H'.trans K').level n) := by
  subst D'
  subst E'
  exact heq_of_eq (Homotopy.trans_level_congr H K H' K' n
    (eq_of_heq hH) (eq_of_heq hK))

/-- Reflexive tracks retain the whole map under both object-presentation equalities. -/
theorem Homotopy.refl_level_congr_objects
    {D D' E E' : LoopPrespectrum.{u}} (eD : D = D') (eE : E = E')
    (f : D ⟶ E) (f' : D' ⟶ E') (hf : HEq f f') (n : ℕ) :
    HEq ((Homotopy.refl f).level n) ((Homotopy.refl f').level n) := by
  subst D'
  subst E'
  have h : f = f' := eq_of_heq hf
  subst f'
  rfl

/-- Precomposition retains all three object presentations and the whole supplied track. -/
theorem Homotopy.precomp_level_congr_objects
    {D D' E E' F F' : LoopPrespectrum.{u}}
    (eD : D = D') (eE : E = E') (eF : F = F')
    {a b : E ⟶ F} {a' b' : E' ⟶ F'}
    (h : D ⟶ E) (h' : D' ⟶ E') (hh : HEq h h')
    (H : Homotopy a b) (K : Homotopy a' b') (n : ℕ)
    (hHK : HEq (H.level n) (K.level n)) :
    HEq ((Homotopy.precomp h H).level n) ((Homotopy.precomp h' K).level n) := by
  subst D'
  subst E'
  subst F'
  have eh : h = h' := eq_of_heq hh
  subst h'
  exact heq_of_eq (Homotopy.precomp_level_congr h H K n (eq_of_heq hHK))

/-- Postcomposition retains all three object presentations and the whole supplied track. -/
theorem Homotopy.postcomp_level_congr_objects
    {D D' E E' F F' : LoopPrespectrum.{u}}
    (eD : D = D') (eE : E = E') (eF : F = F')
    {a b : D ⟶ E} {a' b' : D' ⟶ E'}
    (H : Homotopy a b) (K : Homotopy a' b')
    (h : E ⟶ F) (h' : E' ⟶ F') (hh : HEq h h') (n : ℕ)
    (hHK : HEq (H.level n) (K.level n)) :
    HEq ((H.postcomp h).level n) ((K.postcomp h').level n) := by
  subst D'
  subst E'
  subst F'
  have eh : h = h' := eq_of_heq hh
  subst h'
  exact heq_of_eq (Homotopy.postcomp_level_congr H K h n (eq_of_heq hHK))

/-- Transport an actual relative comparison using both object equalities and whole-level HEqs. -/
def Homotopy.RelHomotopy.ofObjectLevels
    {D D' E E' : LoopPrespectrum.{u}} (eD : D' = D) (eE : E' = E)
    {f g : D ⟶ E} {f' g' : D' ⟶ E'} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, HEq (H'.level n) (H.level n))
    (hK : ∀ n, HEq (K'.level n) (K.level n)) : H'.RelHomotopy K' := by
  subst D'
  subst E'
  exact J.ofLevels H' K' (fun n => eq_of_heq (hH n)) (fun n => eq_of_heq (hK n))

end Topology.LoopPrespectrum
