import PfaffianDescent.FiniteDimensionalFunctionEvaluation
import PfaffianDescent.SchemeModuleGlobalSections
import PfaffianDescent.VoisinProperFiniteIncidence

/-!
# Evaluation witnesses for Voisin's fixed linear systems

This file joins the finite-dimensional evaluation argument to the proper
incidence construction used in Voisin's fixed-divisor-class argument.  If a
bad configuration supplies a nonzero member of a linear system vanishing at
all marked points, injective evaluation on one tuple of distinct points
exhibits a configuration outside the bad locus.  Properness then shows that
the generic configuration avoids the locus.

The final variants use the literal vector space of global sections of a
scheme module.  Thus the remaining geometric construction only has to
provide its projective parameter scheme, universal zero family, and the
stated incidence-to-vanishing implication.
-/

namespace PfaffianDescent

open AlgebraicGeometry

universe u

/-- A finite-dimensional system detected by point evaluations supplies a
configuration outside any bad set whose membership produces a nonzero
section vanishing at every selected point. -/
theorem exists_configuration_avoids_of_evaluation_injective
    {K P V X : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (n : ℕ) (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) → X) (bad : Set X)
    (hbad : ∀ e : Fin n ↪ P, configuration e ∈ bad →
      ∃ v : V, v ≠ 0 ∧ ∀ i, evaluation v (e i) = 0) :
    ∃ x : X, x ∉ bad := by
  obtain ⟨e, he⟩ := exists_embedding_evaluation_injective
    evaluation hevaluation n hrank
  refine ⟨configuration e, ?_⟩
  intro hmem
  obtain ⟨v, hv, hz⟩ := hbad e hmem
  apply hv
  apply he
  funext i
  change evaluation v (e i) = evaluation 0 (e i)
  rw [map_zero]
  exact hz i

/-- Extension-stable form of the good-configuration argument.  Membership in
the bad locus may produce a section over the residue field of a projective
parameter, rather than over `K` itself.  It is enough to show that such
membership would contradict injectivity of the basis-evaluation matrix after
some field extension. -/
theorem exists_configuration_avoids_of_scalarExtension_evaluation
    {K P V X : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (n : ℕ) (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) → X) (bad : Set X)
    (hbad : ∀ e : Fin n ↪ P, configuration e ∈ bad →
      ¬ ∀ {L : Type u} [Field L] (g : K →+* L),
        Function.Injective
          (fun c : Fin (Module.finrank K V) → L => fun i =>
            ∑ j, g (evaluation (Module.finBasis K V j) (e i)) * c j)) :
    ∃ x : X, x ∉ bad := by
  obtain ⟨e, he⟩ :=
    exists_embedding_basisEvaluation_injective_after_fieldExtension_of_finrank_le
      evaluation hevaluation n hrank
  exact ⟨configuration e, fun hmem => hbad e hmem he⟩

/-- Proper-incidence form of the evaluation argument.  Once incidence with a
projective parameter yields a nonzero section vanishing at the selected
points, one evaluation-injective tuple proves that the bad locus is proper,
so the generic point avoids it. -/
theorem genericFunctionField_avoids_properFiniteIncidence_of_evaluation_injective
    {K P V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    {S X T Y : Scheme.{u}} [IsIntegral X]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ)
    (incidenceMap : Fin n →
      (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y) (hincidence : IsClosed incidence)
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ properFiniteIncidenceBadLocus
        xBase tBase incidenceMap incidence →
      ∃ v : V, v ≠ 0 ∧ ∀ i, evaluation v (e i) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus
        xBase tBase incidenceMap incidence := by
  apply genericFunctionField_closedPoint_avoids_properFiniteIncidence_of_exists
    xBase tBase incidenceMap incidence hincidence
  exact exists_configuration_avoids_of_evaluation_injective
    evaluation hevaluation n hrank configuration
      (properFiniteIncidenceBadLocus xBase tBase incidenceMap incidence) hbad

/-- Closed-universal-zero-family specialization of the preceding theorem. -/
theorem
    genericFunctionField_avoids_properFiniteIncidenceRange_of_evaluation_injective
    {K P V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    {S X T Y Z : Scheme.{u}} [IsIntegral X]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ)
    (incidenceMap : Fin n →
      (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (zeroFamily : Z ⟶ Y) [IsClosedImmersion zeroFamily]
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) →
      ∃ v : V, v ≠ 0 ∧ ∀ i, evaluation v (e i) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) := by
  exact
    genericFunctionField_avoids_properFiniteIncidence_of_evaluation_injective
      xBase tBase n incidenceMap (Set.range zeroFamily)
      zeroFamily.isClosedEmbedding.isClosed_range evaluation hevaluation
      hrank configuration hbad

/-- Scalar-extension-safe generic avoidance.  This is the form appropriate
for a projective universal zero family, whose offending member naturally
lives over the residue field of its parameter. -/
theorem
    genericFunctionField_avoids_properFiniteIncidenceRange_of_scalarExtension_evaluation
    {K P V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    {S X T Y Z : Scheme.{u}} [IsIntegral X]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ)
    (incidenceMap : Fin n →
      (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (zeroFamily : Z ⟶ Y) [IsClosedImmersion zeroFamily]
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) →
      ¬ ∀ {L : Type u} [Field L] (g : K →+* L),
        Function.Injective
          (fun c : Fin (Module.finrank K V) → L => fun i =>
            ∑ j, g (evaluation (Module.finBasis K V j) (e i)) * c j)) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) := by
  apply genericFunctionField_closedPoint_avoids_properFiniteIncidenceRange_of_exists
    xBase tBase incidenceMap zeroFamily
  exact exists_configuration_avoids_of_scalarExtension_evaluation
    evaluation hevaluation n hrank configuration
      (properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily)) hbad

/-- Literal scheme-module-global-section form of the finite evaluation
witness.  This is the `h⁰(M) ≤ n` input in Voisin's argument. -/
theorem exists_schemeModuleGlobalSections_configuration_avoids
    {K P X : Type u} [Field K] [Infinite P]
    {W : Scheme.{u}} (base : W ⟶ Spec (.of K)) (M : W.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (n : ℕ)
    (hrank : Module.finrank K (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → X) (bad : Set X)
    (hbad : ∀ e : Fin n ↪ P, configuration e ∈ bad →
      ∃ s : SchemeModuleGlobalSectionsOver base M,
        s ≠ 0 ∧ ∀ i, evaluation s (e i) = 0) :
    ∃ x : X, x ∉ bad :=
  exists_configuration_avoids_of_evaluation_injective
    evaluation hevaluation n hrank configuration bad hbad

/-- The generic fixed-linear-system avoidance theorem stated with genuine
global sections of a scheme module and a closed universal zero family. -/
theorem
    schemeModuleGlobalSections_generic_avoids_properFiniteIncidenceRange
    {K P : Type u} [Field K] [Infinite P]
    {W S X T Y Z : Scheme.{u}} [IsIntegral X]
    (base : W ⟶ Spec (.of K)) (M : W.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ)
    (incidenceMap : Fin n →
      (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (zeroFamily : Z ⟶ Y) [IsClosedImmersion zeroFamily]
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) →
      ∃ s : SchemeModuleGlobalSectionsOver base M,
        s ≠ 0 ∧ ∀ i, evaluation s (e i) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) :=
  genericFunctionField_avoids_properFiniteIncidenceRange_of_evaluation_injective
    xBase tBase n incidenceMap zeroFamily evaluation hevaluation
      hrank configuration hbad

/-- Scalar-extension-safe version for genuine scheme-module global
sections. -/
theorem
    schemeModuleGlobalSections_generic_avoids_properFiniteIncidenceRange_after_fieldExtension
    {K P : Type u} [Field K] [Infinite P]
    {W S X T Y Z : Scheme.{u}} [IsIntegral X]
    (base : W ⟶ Spec (.of K)) (M : W.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ)
    (incidenceMap : Fin n →
      (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (zeroFamily : Z ⟶ Y) [IsClosedImmersion zeroFamily]
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) →
      ¬ ∀ {L : Type u} [Field L] (g : K →+* L),
        Function.Injective
          (fun c : Fin (Module.finrank K
              (SchemeModuleGlobalSectionsOver base M)) → L => fun i =>
            ∑ j, g (evaluation
              (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) j)
              (e i)) * c j)) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) :=
  genericFunctionField_avoids_properFiniteIncidenceRange_of_scalarExtension_evaluation
    xBase tBase n incidenceMap zeroFamily evaluation hevaluation
      hrank configuration hbad

end PfaffianDescent
