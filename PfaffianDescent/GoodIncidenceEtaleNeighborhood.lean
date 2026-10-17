import PfaffianDescent.GoodChartJacobian
import PfaffianDescent.GoodIncidenceFiber
import PfaffianDescent.ProperEtaleShrinking

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]
attribute [local instance] goodChartAlgebra goodTripleBaseAlgebra goodChartModule

/-- The principal open where the incidence chart projection has invertible Jacobian. -/
noncomputable def goodJacobianChart : Scheme.{u} :=
  Spec (.of (Localization.Away (goodChartJacobian K)))

noncomputable def goodJacobianChartι : goodJacobianChart K ⟶ incidenceGraphScheme K :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (IncidenceGraphRing K) (Localization.Away (goodChartJacobian K))))

instance goodJacobianChartι_open : IsOpenImmersion (goodJacobianChartι K) := by
  exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (IncidenceGraphRing K))
    (goodChartJacobian K)

lemma goodJacobianChart_projection_etale :
    Etale (goodJacobianChartι K ≫ incidenceChartToTriples K goodChartPermutation) := by
  haveI := goodChartJacobian_etale K
  have he : goodJacobianChartι K ≫ incidenceChartToTriples K goodChartPermutation =
      Spec.map (CommRingCat.ofHom
        (algebraMap (AlternatingTripleRing K) (Localization.Away (goodChartJacobian K)))) := by
    change Spec.map (CommRingCat.ofHom
        (algebraMap (IncidenceGraphRing K) (Localization.Away (goodChartJacobian K)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (AlternatingTripleRing K) (IncidenceGraphRing K))) = _
    rw [← Spec.map_comp]
    congr 1
  rw [he]
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

lemma goodChartTensor_range_subset_jacobianChart :
    Set.range (goodChartTensorToChart K) ⊆ Set.range (goodJacobianChartι K) := by
  change Set.range (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : IncidenceGraphRing K →ₐ[AlternatingTripleRing K]
        GoodChartTensorFiber K).toRingHom) ⊆
    Set.range (PrimeSpectrum.comap
      (algebraMap (IncidenceGraphRing K) (Localization.Away (goodChartJacobian K))))
  rw [PrimeSpectrum.localization_away_comap_range _ (goodChartJacobian K)]
  exact presentation_fiber_image_subset_jacobianOpen (goodChartSquarePresentation K) K

lemma goodGraphFiber_range_subset_jacobianChart :
    Set.range (goodGraphFiberToIncidenceChart K) ⊆ Set.range (goodJacobianChartι K) := by
  have he : (goodChartTensorFiberIso K).inv ≫ goodChartTensorToChart K =
      goodGraphFiberToIncidenceChart K :=
    (goodChartTensorFiberIso K).inv_comp_eq.mpr (goodChartTensorFiberIso_toChart K).symm
  rintro _ ⟨p, rfl⟩
  have hp := goodChartTensor_range_subset_jacobianChart K
    (Set.mem_range_self ((goodChartTensorFiberIso K).inv p))
  exact (congrArg (fun f : goodGraphFiberScheme K ⟶ incidenceGraphScheme K => f p) he) ▸ hp

/-- An actual open subscheme of the full incidence scheme on which the projection is étale. -/
noncomputable def goodJacobianIncidenceι : goodJacobianChart K ⟶ incidenceScheme K :=
  goodJacobianChartι K ≫ incidenceChartι K goodChartPermutation

instance goodJacobianIncidenceι_open : IsOpenImmersion (goodJacobianIncidenceι K) := by
  dsimp only [goodJacobianIncidenceι]
  infer_instance

instance goodJacobianIncidence_projection_etale :
    Etale (goodJacobianIncidenceι K ≫ incidenceToTriples K) := by
  change Etale ((goodJacobianChartι K ≫ incidenceChartι K goodChartPermutation) ≫ incidenceToTriples K)
  rw [Category.assoc, incidenceChartι_toTriples]
  exact goodJacobianChart_projection_etale K

/-- This étale open contains the entire scheme-theoretic fiber over the displayed triple. -/
lemma goodIncidenceFiber_range_subset_jacobian :
    Set.range (pullback.fst (incidenceToTriples K) (goodTripleSection K)) ⊆
      Set.range (goodJacobianIncidenceι K) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := goodGraphFiberToGlobalFiber_surjective K x
  obtain ⟨y, hy⟩ := goodGraphFiber_range_subset_jacobianChart K (Set.mem_range_self p)
  refine ⟨y, ?_⟩
  calc
    goodJacobianIncidenceι K y = incidenceChartι K goodChartPermutation (goodJacobianChartι K y) := rfl
    _ = incidenceChartι K goodChartPermutation (goodGraphFiberToIncidenceChart K p) :=
      congrArg (incidenceChartι K goodChartPermutation) hy
    _ = pullback.fst (incidenceToTriples K) (goodTripleSection K) (goodGraphFiberToGlobalFiber K p) :=
      (congrArg (fun f : goodGraphFiberScheme K ⟶ incidenceScheme K => f p)
        (goodGraphFiberToGlobalFiber_toIncidence K)).symm

/-- A nonempty open neighborhood of the displayed triple on which the global projection is finite étale. -/
noncomputable def goodFiniteEtaleOpen : (alternatingTripleScheme K).Opens :=
  properTargetOpen (incidenceToTriples K) (goodJacobianIncidenceι K)

lemma goodFiniteEtaleOpen_contains_good :
    Set.range (goodTripleSection K) ⊆ (goodFiniteEtaleOpen K : Set (alternatingTripleScheme K)) :=
  properTargetOpen_contains_image (incidenceToTriples K) (goodJacobianIncidenceι K)
    (goodTripleSection K) (goodIncidenceFiber_range_subset_jacobian K)

instance goodFiniteEtaleOpen_finite : IsFinite (incidenceToTriples K ∣_ goodFiniteEtaleOpen K) :=
  properTargetOpen_finite (incidenceToTriples K) (goodJacobianIncidenceι K)

instance goodFiniteEtaleOpen_etale : Etale (incidenceToTriples K ∣_ goodFiniteEtaleOpen K) :=
  properTargetOpen_etale (incidenceToTriples K) (goodJacobianIncidenceι K)

lemma goodFiniteEtaleOpen_nonempty : (goodFiniteEtaleOpen K : Set (alternatingTripleScheme K)).Nonempty :=
  ⟨goodTripleSection K (IsLocalRing.closedPoint K),
    goodFiniteEtaleOpen_contains_good K (Set.mem_range_self _)⟩

end
end PfaffianDescent
