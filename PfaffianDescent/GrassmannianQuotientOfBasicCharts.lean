import PfaffianDescent.GrassmannianCoordinateFunctor
import Mathlib.RingTheory.LocalProperties.FinitePresentation

namespace PfaffianDescent
open TensorProduct Module
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {m n : ℕ}
  (W : Submodule R ((Fin m → R) × (Fin n → R)))

/-- A graph chart identifies the tensor quotient with the standard free quotient. -/
noncomputable def grassmannianQuotientTensorEquivOfChart
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) S)
    (hT : grassmannianSubmoduleBaseChange (algebraMap R S) W = grassmannianChartSubmodule S σ T) :
    S ⊗[R] (((Fin m → R) × (Fin n → R)) ⧸ W) ≃ₗ[S] (Fin n → S) :=
  (grassmannianBaseChangeQuotientEquiv R S m n W).symm.trans
    ((Submodule.quotEquivOfEq _ _ hT).trans (grassmannianChartQuotientEquiv S σ T))

end
section
variable (R : Type*) [CommRing R] {m n : ℕ}
  (W : Submodule R ((Fin m → R) × (Fin n → R)))
  (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
  (hcharts : ∀ a : s, ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) (Localization.Away a.1)),
    grassmannianSubmoduleBaseChange (algebraMap R (Localization.Away a.1)) W =
      grassmannianChartSubmodule (Localization.Away a.1) σ T)

include hs hcharts

lemma grassmannianBasicCharts_atPrime (p : PrimeSpectrum R) :
    ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
      (T : Matrix (Fin n) (Fin m) (Localization.AtPrime p.asIdeal)),
      grassmannianSubmoduleBaseChange (algebraMap R (Localization.AtPrime p.asIdeal)) W =
        grassmannianChartSubmodule (Localization.AtPrime p.asIdeal) σ T := by
  classical
  have ha : ∃ a : s, a.1 ∉ p.asIdeal := by
    by_contra! h
    have hle : Ideal.span (s : Set R) ≤ p.asIdeal := Ideal.span_le.mpr (fun x hx => h ⟨x, hx⟩)
    rw [hs] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨a, ha⟩ := ha
  obtain ⟨σ, T, hT⟩ := hcharts a
  let S := Localization.AtPrime p.asIdeal
  have hu : IsUnit (algebraMap R S a.1) := IsLocalization.map_units S (⟨a.1, ha⟩ : p.asIdeal.primeCompl)
  let φ : Localization.Away a.1 →+* S := IsLocalization.Away.lift a.1 hu
  have hφ : φ.comp (algebraMap R (Localization.Away a.1)) = algebraMap R S :=
    IsLocalization.Away.lift_comp a.1 hu
  refine ⟨σ, T.map φ, ?_⟩
  calc
    grassmannianSubmoduleBaseChange (algebraMap R S) W =
        grassmannianSubmoduleBaseChange φ (grassmannianSubmoduleBaseChange
          (algebraMap R (Localization.Away a.1)) W) := by
      rw [grassmannianSubmoduleBaseChange_comp, hφ]
    _ = grassmannianSubmoduleBaseChange φ (grassmannianChartSubmodule _ σ T) :=
      congrArg (grassmannianSubmoduleBaseChange φ) hT
    _ = _ := grassmannianChartSubmodule_baseChange φ σ T

lemma grassmannianBasicCharts_finitePresentation :
    Module.FinitePresentation R (((Fin m → R) × (Fin n → R)) ⧸ W) := by
  let Q := ((Fin m → R) × (Fin n → R)) ⧸ W
  apply Module.FinitePresentation.of_localizationSpan' (s : Set R) hs
    (Rₚ := fun a => Localization.Away a.1)
    (Mₚ := fun a => Localization.Away a.1 ⊗[R] Q)
    (fun a => TensorProduct.mk R (Localization.Away a.1) Q 1)
  intro a
  obtain ⟨σ, T, hT⟩ := hcharts a
  haveI : Module.FinitePresentation (Localization.Away a.1) (Fin n → Localization.Away a.1) :=
    Module.finitePresentation_of_projective _ _
  exact Module.FinitePresentation.of_equiv (grassmannianQuotientTensorEquivOfChart R _ W σ T hT).symm

/-- A finite covering by genuine graph quotients gives a finite projective quotient of constant rank. -/
noncomputable def grassmannianQuotientOfBasicCharts :
    Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n where
  toSubmodule := W
  finite_quotient := inferInstance
  projective_quotient := by
    haveI := grassmannianBasicCharts_finitePresentation R W s hs hcharts
    apply Module.freeLocus_eq_univ_iff.mp
    apply Set.eq_univ_iff_forall.mpr
    intro p
    apply (Module.mem_freeLocus_iff_tensor p (Localization.AtPrime p.asIdeal)).mpr
    obtain ⟨σ, T, hT⟩ := grassmannianBasicCharts_atPrime R W s hs hcharts p
    exact Module.Free.of_equiv (grassmannianQuotientTensorEquivOfChart R _ W σ T hT).symm
  rankAtStalk_eq p := by
    obtain ⟨σ, T, hT⟩ := grassmannianBasicCharts_atPrime R W s hs hcharts p
    rw [Module.rankAtStalk_eq_finrank_tensorProduct,
      (grassmannianQuotientTensorEquivOfChart R _ W σ T hT).finrank_eq]
    simp

end
end PfaffianDescent
