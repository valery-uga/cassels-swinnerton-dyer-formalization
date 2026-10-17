import PfaffianDescent.IncidenceChartSectionCoordinates

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}

lemma incidenceChartProductIso_function (a : X ⟶ incidenceGraphScheme K) (i : IncidenceFiberIndex) :
    affineFunctionHom (a ≫ (incidenceChartProductIso K).hom) (MvPolynomial.X i) =
      affineFunctionHom a (MvPolynomial.X (Sum.inr i)) := by
  have hi : (incidenceChartProductAlgEquiv K).symm (MvPolynomial.X i) = MvPolynomial.X (Sum.inr i) := by
    apply (incidenceChartProductAlgEquiv K).injective
    rw [AlgEquiv.apply_symm_apply, incidenceChartProductAlgEquiv_inr]
  have h := RingHom.congr_fun (affineFunctionHom_comp_Spec a
    (incidenceChartProductAlgEquiv K).symm.toRingHom) (MvPolynomial.X i)
  exact h.trans (congrArg (affineFunctionHom a) hi)

variable (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (g : X ⟶ grassmannianChartScheme K 3 3)

noncomputable def incidenceSectionChartLift
    (f : X ⟶ incidenceScheme K)
    (hf : f ≫ incidenceToGrassmannian K = g ≫ grassmannianChartι K σ) : X ⟶ incidenceGraphScheme K :=
  (incidenceGrassmannianChart_isPullback K σ).lift g f hf.symm

lemma incidenceSectionChartLift_toGraph
    (f : X ⟶ incidenceScheme K)
    (hf : f ≫ incidenceToGrassmannian K = g ≫ grassmannianChartι K σ) :
    incidenceSectionChartLift K σ g f hf ≫ incidenceGraphToGrassmannianChart K = g :=
  (incidenceGrassmannianChart_isPullback K σ).lift_fst _ _ _

lemma incidenceSectionChartLift_toIncidence
    (f : X ⟶ incidenceScheme K)
    (hf : f ≫ incidenceToGrassmannian K = g ≫ grassmannianChartι K σ) :
    incidenceSectionChartLift K σ g f hf ≫ incidenceChartι K σ = f :=
  (incidenceGrassmannianChart_isPullback K σ).lift_snd _ _ _

lemma incidenceChartSectionCoordinates_apply
    (f : {f : X ⟶ incidenceScheme K // f ≫ incidenceToGrassmannian K = g ≫ grassmannianChartι K σ})
    (i : IncidenceFiberIndex) :
    incidenceChartSectionCoordinates K σ g f i =
      incidenceGraphPointCoordinates Γ(X, ⊤)
        (incidenceChartPoint K (incidenceSectionChartLift K σ g f.1 f.2)) (Sum.inr i) := by
  change affineFunctionHom (incidenceSectionChartLift K σ g f.1 f.2 ≫
    (incidenceChartProductIso K).hom) (MvPolynomial.X i) = _
  exact (incidenceChartProductIso_function K _ i).trans
    (congrFun (incidenceChartPoint_coordinates K (incidenceSectionChartLift K σ g f.1 f.2)) (Sum.inr i)).symm

end
end PfaffianDescent
