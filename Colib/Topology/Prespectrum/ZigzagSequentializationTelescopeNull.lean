/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationHomotopy
public import Colib.Topology.Prespectrum.ZigzagSequentializationMapLaws

/-! # Whole nullhomotopies on the actual zigzag telescope

The original vertex and target nullhomotopies descend through the actual recursive stages
and telescope cylinders. The zero endpoint is a proved strict map equality.
-/
@[expose] public section
noncomputable section
open Topology Topology.LoopPrespectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (E' V' : ℕ → LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)

/-- Zero input maps induce the literal zero map on the genuine recursive telescope. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationTelescopeNull.lean:30"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inducedTelescopeMap_zero :
    inducedTelescopeMap E V a b E' V' a' b' (fun i ↦ zeroHom (E i) (E' i))
      (fun i ↦ zeroHom (V i) (V' i))
      (fun i ↦ by
        apply LoopPrespectrum.Hom.ext; funext k; ext _x
        exact (a' i).map_point k |>.symm)
      (fun i ↦ by
        apply LoopPrespectrum.Hom.ext; funext k; ext _x
        exact (b' i).map_point k |>.symm) =
        zeroHom (Telescope.prespectrum (stage E V a b) (transition E V a b))
          (Telescope.prespectrum (stage E' V' a' b') (transition E' V' a' b')) := by
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder (stage E' V' a' b') (transition E' V' a' b') k i
      (s, (stageMap E V a b E' V' a' b' _ _ _ _ i).map k x) = _
  rw [stageMap_zero]
  exact Telescope.cylinder_point _ _ k i s

variable (d₀ : ∀ n, E n ⟶ E' n) (v₀ : ∀ n, V n ⟶ V' n)
    (ha₀ : ∀ n, a n ≫ v₀ n = d₀ n ≫ a' n)
    (hb₀ : ∀ n, b n ≫ v₀ n = d₀ (n + 1) ≫ b' n)

/-- Original whole input nullhomotopies descend to a literal telescope nullhomotopy. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationTelescopeNull.lean:49"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def inducedTelescopeNullhomotopy
    (NE : ∀ n, Homotopy (d₀ n) (zeroHom (E n) (E' n)))
    (NV : ∀ n, Homotopy (v₀ n) (zeroHom (V n) (V' n)))
    (hNA : ∀ n k r x, (NV n).level k (r, (a n).map k x) =
      (a' n).map k ((NE n).level k (r, x)))
    (hNB : ∀ n k r x, (NV n).level k (r, (b n).map k x) =
      (b' n).map k ((NE (n + 1)).level k (r, x))) :
    Homotopy (inducedTelescopeMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀)
      (zeroHom (Telescope.prespectrum (stage E V a b) (transition E V a b))
        (Telescope.prespectrum (stage E' V' a' b') (transition E' V' a' b'))) :=
  (inducedTelescopeHomotopy E V a b E' V' a' b' d₀
    (fun i ↦ zeroHom (E i) (E' i)) v₀ (fun i ↦ zeroHom (V i) (V' i)) ha₀ hb₀
    (fun i ↦ by
        apply LoopPrespectrum.Hom.ext; funext k; ext _x
        exact (a' i).map_point k |>.symm)
    (fun i ↦ by
        apply LoopPrespectrum.Hom.ext; funext k; ext _x
        exact (b' i).map_point k |>.symm)
    NE NV hNA hNB).cast rfl (inducedTelescopeMap_zero E V a b E' V' a' b')


/-- The genuine telescope maps preserve the original composite input maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationTelescopeNull.lean:67"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inducedTelescopeMap_comp
    (E'' V'' : ℕ → LoopPrespectrum.{u})
    (a'' : ∀ n, E'' n ⟶ V'' n) (b'' : ∀ n, E'' (n + 1) ⟶ V'' n)
    (d' : ∀ n, E' n ⟶ E'' n) (v' : ∀ n, V' n ⟶ V'' n)
    (ha' : ∀ n, a' n ≫ v' n = d' n ≫ a'' n)
    (hb' : ∀ n, b' n ≫ v' n = d' (n + 1) ≫ b'' n) :
    inducedTelescopeMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀ ≫
        inducedTelescopeMap E' V' a' b' E'' V'' a'' b'' d' v' ha' hb' =
      inducedTelescopeMap E V a b E'' V'' a'' b''
        (fun i => d₀ i ≫ d' i) (fun i => v₀ i ≫ v' i)
        (fun i => by rw [← Category.assoc, ha₀, Category.assoc, ha', Category.assoc])
        (fun i => by rw [← Category.assoc, hb₀, Category.assoc, hb', Category.assoc]) := by
  apply Telescope.hom_ext
  intro k i s x
  change (inducedTelescopeMap E' V' a' b' E'' V'' a'' b'' d' v' ha' hb').map k
      ((inducedTelescopeMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀).map k
        (Telescope.cylinder (stage E V a b) (transition E V a b) k i (s, x))) = _
  simp only [inducedTelescopeMap, Telescope.map_cylinder]
  exact congrArg (fun g => Telescope.cylinder (stage E'' V'' a'' b'')
    (transition E'' V'' a'' b'') k i (s, g.map k x))
      (stageMap_comp E V a b E' V' a' b' d₀ v₀ ha₀ hb₀
        E'' V'' a'' b'' d' v' ha' hb' i)

end Topology.LoopPrespectrum.ZigzagSequentialization
