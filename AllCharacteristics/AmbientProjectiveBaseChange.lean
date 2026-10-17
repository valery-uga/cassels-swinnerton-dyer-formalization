import AllCharacteristics.AmbientChartPresentation
import AllCharacteristics.ProjectiveBaseChange

/-!
# Coefficient base change for ordinary ambient projective space

The explicit polynomial quotient presentation of each ordinary ambient chart
identifies coefficient change with an affine pushout. These local squares
glue to the global projective base-change square.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective

universe u
variable {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ R
local notation "𝓑" => MvPolynomial.homogeneousSubmodule σ S

variable (f : R →+* S)

/-- The equation `X j = 1` is preserved by coefficient change. -/
theorem ambientChartPresentationIdeal_map (j : σ) :
    (ambientChartPresentationIdeal (R := R) j).map (MvPolynomial.map f) =
      ambientChartPresentationIdeal (R := S) j := by
  simp only [ambientChartPresentationIdeal, Ideal.map_span,
    Set.image_singleton, map_sub, map_X, map_one]

/-- The quotient obtained after changing coefficients is the actual ambient
projective coordinate chart over the new ring. -/
noncomputable def ambientChartBaseChangePresentationEquiv (j : σ) :
    (MvPolynomial σ S ⧸
      (ambientChartPresentationIdeal (R := R) j).map (MvPolynomial.map f)) ≃+*
      Away 𝓑 (MvPolynomial.X j) :=
  (Ideal.quotEquivOfEq (ambientChartPresentationIdeal_map f j)).trans
    (ambientChartPresentationEquiv (R := S) j)

/-- The changed presentation sends a polynomial class to normalized
evaluation over the new coefficient ring. -/
theorem ambientChartBaseChangePresentationEquiv_mk (j : σ)
    (p : MvPolynomial σ S) :
    ambientChartBaseChangePresentationEquiv f j
      (Ideal.Quotient.mk
        ((ambientChartPresentationIdeal (R := R) j).map (MvPolynomial.map f)) p) =
      ambientChartEvaluation j p := by
  exact (congrArg (ambientChartPresentationEquiv (R := S) j)
    (Ideal.quotEquivOfEq_mk (ambientChartPresentationIdeal_map f j) p)).trans
      (ambientChartPresentationEquiv_mk j p)

/-- The coefficient map on ambient charts obtained from their polynomial
quotient presentations. -/
noncomputable def ambientChartPresentationCoefficientMap (j : σ) :
    Away 𝒜 (MvPolynomial.X j) →+* Away 𝓑 (MvPolynomial.X j) :=
  (ambientChartBaseChangePresentationEquiv f j).toRingHom.comp
    ((PolynomialQuotient.coefficientMap f (ambientChartPresentationIdeal j)).comp
      (ambientChartPresentationEquiv (R := R) j).symm.toRingHom)

/-- The presentation coefficient map changes only polynomial coefficients
in normalized evaluation. -/
theorem ambientChartPresentationCoefficientMap_eval (j : σ)
    (p : MvPolynomial σ R) :
    ambientChartPresentationCoefficientMap f j (ambientChartEvaluation j p) =
      ambientChartEvaluation j (p.map f) := by
  rw [← ambientChartPresentationEquiv_mk j p]
  change ambientChartBaseChangePresentationEquiv f j
    (PolynomialQuotient.coefficientMap f (ambientChartPresentationIdeal j)
      ((ambientChartPresentationEquiv (R := R) j).symm
        ((ambientChartPresentationEquiv (R := R) j)
          (Ideal.Quotient.mk _ p)))) = _
  rw [RingEquiv.symm_apply_apply, PolynomialQuotient.coefficientMap_mk,
    ambientChartBaseChangePresentationEquiv_mk]

/-- The existing ambient coefficient map acts by coefficient change on all
normalized polynomial evaluations. -/
theorem ambientCoefficientChartMap_eval (j : σ) (p : MvPolynomial σ R) :
    ambientCoefficientChartMap f j (ambientChartEvaluation j p) =
      ambientChartEvaluation j (p.map f) := by
  have h : (ambientCoefficientChartMap f j).comp (ambientChartEvaluation j) =
      (ambientChartEvaluation j).comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, ambientChartEvaluation, eval₂Hom_C, map_C]
      exact ambientCoefficientChartMap_baseMap f j r
    · intro i
      simp only [RingHom.comp_apply, ambientChartEvaluation, eval₂Hom_X', map_X]
      exact ambientCoefficientChartMap_coordinate f j i
  exact DFunLike.congr_fun h p

/-- The coefficient map constructed from the polynomial presentation agrees
with the global Proj coefficient map on every ambient coordinate chart. -/
theorem ambientChartPresentationCoefficientMap_eq (j : σ) :
    ambientChartPresentationCoefficientMap f j = ambientCoefficientChartMap f j := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective j z
  exact (ambientChartPresentationCoefficientMap_eval f j p).trans
    (ambientCoefficientChartMap_eval f j p).symm

/-- Changing coefficients on an ordinary ambient coordinate chart is a
categorical pushout of commutative rings. -/
theorem isPushout_ambientCoefficientChartMap (j : σ) :
    IsPushout
      (CommRingCat.ofHom (GradedChart.baseMap 𝒜 (z := MvPolynomial.X j)))
      (CommRingCat.ofHom f)
      (CommRingCat.ofHom (ambientCoefficientChartMap f j))
      (CommRingCat.ofHom (GradedChart.baseMap 𝓑 (z := MvPolynomial.X j))) := by
  rw [← ambientChartPresentationCoefficientMap_eq f j]
  apply (PolynomialQuotient.isPushout f
    (ambientChartPresentationIdeal (R := R) j)).of_iso
    (Iso.refl _) (ambientChartPresentationEquiv (R := R) j).toCommRingCatIso
    (Iso.refl _) (ambientChartBaseChangePresentationEquiv f j).toCommRingCatIso
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (ambientChartPresentationEquiv_mk j (MvPolynomial.C r)).trans
      (MvPolynomial.eval₂_C _ _ _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change ambientChartBaseChangePresentationEquiv f j
      (PolynomialQuotient.coefficientMap f (ambientChartPresentationIdeal j) x) =
      ambientChartBaseChangePresentationEquiv f j
        (PolynomialQuotient.coefficientMap f (ambientChartPresentationIdeal j)
          ((ambientChartPresentationEquiv (R := R) j).symm
            ((ambientChartPresentationEquiv (R := R) j) x)))
    rw [RingEquiv.symm_apply_apply]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact (ambientChartBaseChangePresentationEquiv_mk f j (MvPolynomial.C s)).trans
      (MvPolynomial.eval₂_C _ _ _)

/-- The affine schemes of corresponding ambient coordinate charts form a
Cartesian square under coefficient change. -/
theorem isPullback_ambientCoefficientChartMap (j : σ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (ambientCoefficientChartMap f j)))
      (Spec.map (CommRingCat.ofHom
        (GradedChart.baseMap 𝓑 (z := MvPolynomial.X j))))
      (Spec.map (CommRingCat.ofHom
        (GradedChart.baseMap 𝒜 (z := MvPolynomial.X j))))
      (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_ambientCoefficientChartMap f j)

/-- The structure map on a standard ambient projective coordinate chart is
its explicit coefficient map. -/
theorem ambientCoordinateChart_toBase {T : Type u} [CommRing T] (j : σ) :
    Proj.awayι (MvPolynomial.homogeneousSubmodule σ T) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X T j) (by decide : 0 < 1) ≫
        ambientToBase (R := T) (σ := σ) =
      Spec.map (CommRingCat.ofHom
        (GradedChart.baseMap (MvPolynomial.homogeneousSubmodule σ T)
          (z := MvPolynomial.X j))) := by
  let hx : MvPolynomial.X j ∈ (MvPolynomial.homogeneousSubmodule σ T) 1 :=
    MvPolynomial.isHomogeneous_X T j
  change Proj.awayι (MvPolynomial.homogeneousSubmodule σ T) (MvPolynomial.X j)
      hx Nat.zero_lt_one ≫
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ T) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap T ((MvPolynomial.homogeneousSubmodule σ T) 0)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Ordinary ambient projective space commutes with arbitrary coefficient
base change as an actual Cartesian square of schemes. -/
theorem isPullback_ambientCoefficientMap :
    IsPullback (ambientCoefficientMap (σ := σ) f)
      (ambientToBase (R := S) (σ := σ))
      (ambientToBase (R := R) (σ := σ))
      (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _
    (ambientCoordinateOpenCover (R := R) (σ := σ)).openCover
  intro j
  change σ at j
  change IsPullback
    (pullback.snd (ambientCoefficientMap (σ := σ) f)
      (Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
        (by decide : 0 < 1)))
    (pullback.fst (ambientCoefficientMap (σ := σ) f)
      (Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
        (by decide : 0 < 1)) ≫ ambientToBase (R := S) (σ := σ))
    (Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
      (by decide : 0 < 1) ≫ ambientToBase (R := R) (σ := σ))
    (Spec.map (CommRingCat.ofHom f))
  have hc := (isPullback_ambientCoefficientMap_chart f j).flip
  have hb := isPullback_ambientCoefficientChartMap f j
  rw [← ambientCoordinateChart_toBase (T := R) j,
    ← ambientCoordinateChart_toBase (T := S) j] at hb
  apply hb.of_iso hc.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using hc.isoPullback_hom_snd.symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun a ↦ a ≫ ambientToBase (R := S) (σ := σ))
        hc.isoPullback_hom_fst.symm
  · simp
  · simp

end HomogeneousProjective
end AllCharacteristics
