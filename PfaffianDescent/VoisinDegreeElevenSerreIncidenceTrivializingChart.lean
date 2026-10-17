import PfaffianDescent.VoisinDegreeElevenSerreIncidenceRelativeEvaluation
import Mathlib.Tactic.FinCases

/-! # Actual simultaneous bundle charts for three marked points -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {X B : Scheme.{u}} {M : X.Modules} {ι : Type u}

def serreThreePointTrivializingOpen
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (marked : Fin 3 → (B ⟶ X)) (chart : Fin 3 → C.ι) : B.Opens :=
  (marked 0 ⁻¹ᵁ C.U (chart 0)) ⊓
    ((marked 1 ⁻¹ᵁ C.U (chart 1)) ⊓ (marked 2 ⁻¹ᵁ C.U (chart 2)))

theorem serreThreePointTrivializingOpen_mem_iff
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (marked : Fin 3 → (B ⟶ X)) (chart : Fin 3 → C.ι) (b : B) :
    b ∈ serreThreePointTrivializingOpen C marked chart ↔
      ∀ i, marked i b ∈ C.U (chart i) := by
  change (_ ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 0, h 1, h 2⟩

/-- The affine free cover itself supplies compatible chart indices around
every actual triple configuration. -/
theorem serreThreePointTrivializingOpen_exists_at
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (marked : Fin 3 → (B ⟶ X)) (b : B) :
    ∃ chart : Fin 3 → C.ι, b ∈ serreThreePointTrivializingOpen C marked chart := by
  have h : ∀ i : Fin 3, ∃ j : C.ι, marked i b ∈ C.U j := by
    intro i
    have hx : marked i b ∈ ⨆ j, C.U j := by rw [C.covers]; trivial
    exact Opens.mem_iSup.mp hx
  choose chart hchart using h
  exact ⟨chart, (serreThreePointTrivializingOpen_mem_iff C marked chart b).mpr hchart⟩

/-- The three marked morphisms literally factor through their bundle charts
on the constructed common configuration open. -/
def serreThreePointTrivializingMarked
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (marked : Fin 3 → (B ⟶ X)) (chart : Fin 3 → C.ι) (i : Fin 3) :
    (serreThreePointTrivializingOpen C marked chart).toScheme ⟶
      (C.U (chart i)).toScheme :=
  IsOpenImmersion.lift (C.U (chart i)).ι
    ((serreThreePointTrivializingOpen C marked chart).ι ≫ marked i) (by
      rintro x ⟨b, rfl⟩
      rw [(C.U (chart i)).range_ι]
      exact (serreThreePointTrivializingOpen_mem_iff C marked chart b.1).mp b.2 i)

@[reassoc] theorem serreThreePointTrivializingMarked_comp
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (marked : Fin 3 → (B ⟶ X)) (chart : Fin 3 → C.ι) (i : Fin 3) :
    serreThreePointTrivializingMarked C marked chart i ≫ (C.U (chart i)).ι =
      (serreThreePointTrivializingOpen C marked chart).ι ≫ marked i :=
  IsOpenImmersion.lift_fac _ _ _

/-- Refining the constructed common open by its actual affine cover gives
an affine configuration chart with all three literal marked factorizations. -/
theorem serreThreePointTrivializingAffineChart_exists_at
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (marked : Fin 3 → (B ⟶ X)) (b : B) :
    ∃ (A : Scheme.{u}) (a : A ⟶ B) (chart : Fin 3 → C.ι)
      (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme),
      IsAffine A ∧ IsOpenImmersion a ∧ b ∈ Set.range a ∧
      ∀ i, markedA i ≫ (C.U (chart i)).ι = a ≫ marked i := by
  obtain ⟨chart, hb⟩ := serreThreePointTrivializingOpen_exists_at C marked b
  let U := serreThreePointTrivializingOpen C marked chart
  let bU : U.toScheme := ⟨b, hb⟩
  obtain ⟨j, y, hy⟩ := U.toScheme.affineCover.exists_eq bU
  let a := U.toScheme.affineCover.f j ≫ U.ι
  let markedA := fun i => U.toScheme.affineCover.f j ≫
    serreThreePointTrivializingMarked C marked chart i
  refine ⟨U.toScheme.affineCover.X j, a, chart, markedA,
    inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨y, ?_⟩
    change (U.toScheme.affineCover.f j ≫ U.ι) y = b
    rw [Scheme.Hom.comp_apply, hy]
    rfl
  · intro i
    dsimp only [markedA, a, U]
    rw [Category.assoc, serreThreePointTrivializingMarked_comp]
    exact (Category.assoc _ _ _).symm

end PfaffianDescent
