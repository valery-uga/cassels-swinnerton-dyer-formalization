import PfaffianDescent.GrassmannianBasicOpenCharts
import PfaffianDescent.GrassmannianLocalModuli
import Mathlib.AlgebraicGeometry.Cover.Open

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable {A : Type u} [CommRing A] {m n : ℕ}

/-- A basic open on which the given quotient has standard graph coordinates. -/
structure GrassmannianBasicChart (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n) where
  denominator : A
  permutation : Equiv.Perm (Fin m ⊕ Fin n)
  matrix : Matrix (Fin n) (Fin m) (Localization.Away denominator)
  submodule_eq : grassmannianSubmoduleBaseChange (algebraMap A (Localization.Away denominator)) W.toSubmodule =
    grassmannianChartSubmodule (Localization.Away denominator) permutation matrix

lemma grassmannianBasicChart_exists
    (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n) (p : PrimeSpectrum A) :
    ∃ d : GrassmannianBasicChart W, d.denominator ∉ p.asIdeal := by
  obtain ⟨a, ha, σ, T, hT⟩ := grassmannian_quotient_exists_basic_chart A W p
  exact ⟨⟨a, σ, T, hT⟩, ha⟩

noncomputable def grassmannianBasicChartAt
    (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n) (p : PrimeSpectrum A) :
    GrassmannianBasicChart W := (grassmannianBasicChart_exists W p).choose

lemma grassmannianBasicChartAt_notMem
    (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n) (p : PrimeSpectrum A) :
    (grassmannianBasicChartAt W p).denominator ∉ p.asIdeal :=
  (grassmannianBasicChart_exists W p).choose_spec

/-- A covering of the entire affine base by genuine quotient graph charts. -/
noncomputable def grassmannianQuotientOpenCover
    (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n) :
    Scheme.OpenCover.{u} (Spec (.of A)) where
  I₀ := PrimeSpectrum A
  X p := Spec (.of (Localization.Away (grassmannianBasicChartAt W p).denominator))
  f p := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (grassmannianBasicChartAt W p).denominator)))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      refine ⟨x, ?_⟩
      have hr := PrimeSpectrum.localization_away_comap_range
        (Localization.Away (grassmannianBasicChartAt W x).denominator)
        (grassmannianBasicChartAt W x).denominator
      exact (eq_iff_iff.mp congr(x ∈ $hr)).mpr (grassmannianBasicChartAt_notMem W x)
    · intro p
      infer_instance

end
end PfaffianDescent
