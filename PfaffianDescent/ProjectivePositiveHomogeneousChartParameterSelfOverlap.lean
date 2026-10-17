import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterOverlap

/-! The actual chart's universal entire family lies in its own chart, so
its constructed parameter self-overlap is the WHOLE original representer.
This uses accepted native315 and the all-test overlap criterion, with no
transition or gluing hypothesis. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The SAME classifier's constructed self-overlap is the whole parameter
scheme. Containment of the entire universal source follows from the actual
original chart embedding, preserving its complete ideal and nilpotents. -/
theorem relativeOpenChartParameterSelfOverlap_eq_top001
    {X B : Scheme.{u}} (F : X ⟶ B) (U : X.Opens) (n : ℕ) [IsSeparated F]
    (H : Over B)
    (eta : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj H) :
    relativeOpenChartParameterOverlap001 F U U n H eta = ⊤ := by
  have hWhole :
      Set.range (relativeOpenChartClassifiedAmbientPoint001 F U n H eta H (𝟙 H)).val.subschemeι ⊆
        (pullback.snd H.hom F ⁻¹ᵁ U : (pullback H.hom F).Opens) := by
    have hRange := ((relativeOpenContainedPointEquiv315 U F n H)
      (eta.inv.app (.op H) (𝟙 H))).property
    have hIdeal :
        ((relativeOpenContainedPointEquiv315 U F n H)
          (eta.inv.app (.op H) (𝟙 H))).val.val =
        (relativeOpenFiniteFlatPointPush315 U F n H
          (eta.inv.app (.op H) (𝟙 H))).val :=
      congrArg Subtype.val (relativeOpenContainedPointEquiv_push315 U F n H
        (eta.inv.app (.op H) (𝟙 H)))
    change Set.range (((relativeOpenContainedPointEquiv315 U F n H)
      (eta.inv.app (.op H) (𝟙 H))).val.val).subschemeι ⊆
        Set.range (relativeClosedAmbientTestMap313 U.ι F H) at hRange
    rw [hIdeal] at hRange
    intro x hx
    obtain ⟨z, hz⟩ := hRange hx
    have hProjection : pullback.snd H.hom F
        (relativeClosedAmbientTestMap313 U.ι F H z) =
          U.ι (pullback.snd H.hom (U.ι ≫ F) z) :=
      congrArg (fun f => f z) (relativeClosedAmbientTestMap_toOriginal313 U.ι F H)
    change pullback.snd H.hom F x ∈ U
    rw [← hz, hProjection]
    exact (pullback.snd H.hom (U.ι ≫ F) z).property
  have hRange := (relativeOpenChartParameterOverlap_range_iff_entireFamily001
    F U U n H eta H (𝟙 H)).mpr hWhole
  apply top_unique
  intro x _
  apply hRange
  exact ⟨x, by change (𝟙 H.left) x = x; rfl⟩

/-- Original positive homogeneous chart data constructs ONE genuine
all-test representer and classifier whose ACTUAL self-overlap is top.
Neither a representer nor a self-overlap outcome is supplied as input. -/
theorem originalPositiveHomogeneousChart_exists_selfOverlap_eq_top001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (a : CoordinateRing I) (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d)
    (n : ℕ) (hn : 0 < n) :
    ∃ (H : Over (Spec (.of R)))
      (eta : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj H),
      relativeOpenChartParameterOverlap001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) a) n H eta = ⊤ := by
  obtain ⟨H, ⟨eta⟩⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a d hd ha n hn
  exact ⟨H, eta, relativeOpenChartParameterSelfOverlap_eq_top001
    (toBase I) (Proj.basicOpen (grading I) a) n H eta⟩

end PfaffianDescent
end
