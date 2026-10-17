import PfaffianDescent.CoefficientLocalizationMaps
import PfaffianDescent.IncidenceProjectiveKernels
import PfaffianDescent.GrassmannianCoordinateFunctor

namespace PfaffianDescent
open Module
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  (U : Submonoid R) [IsLocalization U S]

/-- For a finitely generated isotropic submodule, coefficient extension localizes its full restriction kernel. -/
theorem ambientAlternatingKernelLinearMap_isLocalizedModule
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R))) (hW : W.FG) :
    IsLocalizedModule U (ambientAlternatingKernelLinearMap R S W) := by
  obtain ⟨r, v, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hW
  let vs := graphCoefficientMap (algebraMap R S) ∘ v
  let W := Submodule.span R (Set.range v)
  let g := alternatingGeneratorEvaluation (R := R) v
  let h := (alternatingGeneratorEvaluation (R := S) vs).restrictScalars R
  let c := alternatingGeneratorEvaluation_localization_commute R S v
  let F := linearKernelMap (ambientAlternatingLinearMap R S)
    (coefficientFunctionLinearMap R S (Fin r × Fin r)) g h c
  haveI : IsLocalizedModule U F := linearKernelMap_isLocalizedModule U S
    (ambientAlternatingLinearMap R S) (coefficientFunctionLinearMap R S (Fin r × Fin r)) g h c
  let eR : (alternatingRestriction R _ W).ker ≃ₗ[R] g.ker :=
    LinearEquiv.ofEq _ _ (alternatingGeneratorEvaluation_ker v).symm
  have heS : h.ker =
      ((alternatingRestriction S _ (grassmannianSubmoduleBaseChange (algebraMap R S) W)).ker).restrictScalars R := by
    change ((alternatingGeneratorEvaluation vs).ker).restrictScalars R = _
    apply congrArg (Submodule.restrictScalars R)
    exact (alternatingGeneratorEvaluation_ker vs).trans
      (congrArg (fun Z => (alternatingRestriction S _ Z).ker)
        (grassmannianSubmoduleBaseChange_span (algebraMap R S) v).symm)
  let eS : h.ker ≃ₗ[R]
      (alternatingRestriction S _ (grassmannianSubmoduleBaseChange (algebraMap R S) W)).ker :=
    LinearEquiv.ofEq _ _ heS
  haveI : IsLocalizedModule U (F.comp eR.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right U F eR
  haveI : IsLocalizedModule U (eS.toLinearMap.comp (F.comp eR.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv U (F.comp eR.toLinearMap) eS
  have he : ambientAlternatingKernelLinearMap R S W =
      eS.toLinearMap.comp (F.comp eR.toLinearMap) := by
    apply LinearMap.ext
    intro B
    apply Subtype.ext
    rfl
  rw [he]
  infer_instance

end
section
variable (R : Type*) [CommRing R]
  (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) (p : PrimeSpectrum R)

/-- The stalk of the incidence restriction kernel is the actual restriction kernel over the local ring. -/
noncomputable def incidenceKernelLocalizationEquiv :
    LocalizedModule p.asIdeal.primeCompl (IncidenceQuotientKernel R W) ≃ₗ[Localization.AtPrime p.asIdeal]
      IncidenceQuotientKernel (Localization.AtPrime p.asIdeal)
        (grassmannianQuotientMap (algebraMap R (Localization.AtPrime p.asIdeal)) W) := by
  haveI : Module.Finite R W.toSubmodule := finite_submodule_of_projective_quotient W.toSubmodule
  haveI : IsLocalizedModule p.asIdeal.primeCompl
      (ambientAlternatingKernelLinearMap R (Localization.AtPrime p.asIdeal) W.toSubmodule) :=
    ambientAlternatingKernelLinearMap_isLocalizedModule R (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl W.toSubmodule (Module.Finite.iff_fg.mp inferInstance)
  exact (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (IncidenceQuotientKernel R W))
    (ambientAlternatingKernelLinearMap R (Localization.AtPrime p.asIdeal) W.toSubmodule)).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

/-- The finite projective restriction kernel has constant rank twelve at every prime. -/
theorem incidenceQuotientKernel_rankAtStalk : Module.rankAtStalk (IncidenceQuotientKernel R W) p = 12 := by
  change Module.finrank (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl (IncidenceQuotientKernel R W)) = 12
  rw [(incidenceKernelLocalizationEquiv R W p).finrank_eq]
  exact incidenceQuotientKernel_local_rank _ _

/-- The full incidence module of isotropic triples has constant rank thirty-six. -/
theorem incidenceQuotientFiber_rankAtStalk : Module.rankAtStalk (IncidenceQuotientFiber R W) p = 36 := by
  rw [Module.rankAtStalk_pi]
  simp [incidenceQuotientKernel_rankAtStalk, finsum_eq_sum_of_fintype]

end
end PfaffianDescent
