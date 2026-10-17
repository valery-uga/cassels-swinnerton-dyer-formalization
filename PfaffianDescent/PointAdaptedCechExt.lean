import PfaffianDescent.PointAdaptedCechKoszulComparison
import PfaffianDescent.SectionRepresenterCechAugmentationExact
import PfaffianDescent.AugmentedChainSourceNaturality

/-!
# Degree-two Ext from the actual point-adapted Cech cover

The cover's geometric covering theorem discharges augmented exactness and
epimorphy. Its cocycles therefore give actual Ext classes without any
additional exactness inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace PfaffianDescent.PointAdaptedAffineCover

universe u

variable {X : Scheme.{u}}

theorem coversTop (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) :
    (Opens.grothendieckTopology X).CoversTop (opens U x) :=
  (Opens.coversTop_iff X _).mpr (covers U x hx hxclosed)

/-- The original formal-singleton augmentation target of this actual cover. -/
abbrev target (U : X.Opens) (x : X) : X.Modules :=
  (sectionRepresenterCechAugmented X.ringCatSheaf (opens U x) ⊤ isTerminalTop).right

theorem augmentation_exact_and_epi
    (U : X.Opens) (x : X) (hx : x ∈ U) (hxclosed : IsClosed ({x} : Set X)) :
    (sectionRepresenterCechAugmentationShortComplex X.ringCatSheaf
      (opens U x) ⊤ isTerminalTop).Exact ∧
    Epi (sectionRepresenterCechAugmentation X.ringCatSheaf (opens U x) ⊤ isTerminalTop) :=
  sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf (opens U x) (coversTop U x hx hxclosed) ⊤ isTerminalTop

theorem exact_one (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) :
    (ShortComplex.mk
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 2 1)
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 1 0)
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d_comp_d 2 1 0)).Exact := by
  have h := sectionRepresenterCechChain_exactAt_succ_of_coversTop
    X.ringCatSheaf (opens U x) (coversTop U x hx hxclosed) 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  exact h

theorem exact_two (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) :
    (ShortComplex.mk
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 3 2)
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 2 1)
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d_comp_d 3 2 1)).Exact := by
  have h := sectionRepresenterCechChain_exactAt_succ_of_coversTop
    X.ringCatSheaf (opens U x) (coversTop U x hx hxclosed) 1
  rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Send a degree-two cocycle on the actual cover to its augmented Ext class. -/
def degreeTwoToExt (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) [HasExt.{u} X.Modules]
    (Y : X.Modules)
    (z : DegreeTwoCocycle
      ((sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 3 2) (Y := Y)) :
    Ext (target U x) Y 2 := by
  let C := sectionRepresenterCechChain X.ringCatSheaf (opens U x)
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf (opens U x) ⊤ isTerminalTop
  letI : Epi eps := (augmentation_exact_and_epi U x hx hxclosed).2
  exact augmentedChainDegreeTwoToExt
    (target U x) (C.X 0) (C.X 1) (C.X 2) (C.X 3) Y
    eps (C.d 1 0) (C.d 2 1) (C.d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      X.ringCatSheaf (opens U x) ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1)
    (augmentation_exact_and_epi U x hx hxclosed).1
    (exact_one U x hx hxclosed) (exact_two U x hx hxclosed) z

end PfaffianDescent.PointAdaptedAffineCover
