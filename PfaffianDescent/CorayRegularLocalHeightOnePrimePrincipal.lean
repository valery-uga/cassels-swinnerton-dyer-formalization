import PfaffianDescent.CorayTwoGeneratorIdealTensorCriterion
import PfaffianDescent.CorayRegularLocalDimensionTwoParameters
import PfaffianDescent.VoisinSmoothCubicChartLocalRegularity

/-!
# Height-one prime principal generation on an actual regular local surface

The general theorem supplies the missing closed-point principal generator.
Regular parameters and their prime quotients are constructed internally;
the OWN ideal tensor criterion supplies freeness. The actual smooth-cubic
caller uses only existing actual regularity/dimension and native localization
height transport. No local UFD or principal-generation premise is supplied.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open IsLocalRing AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u

/-- A height-one prime in a regular local DOMAIN of dimension at most two
is principal. The maximal-ideal pair, prime parameter, own tensor injection
and own module freeness are derived, not supplied as construction premises. -/
theorem regularLocal_heightOnePrime_isPrincipal_of_dimension_le_two
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime]
    (hheight : P.height = 1) : P.IsPrincipal := by
  have hrank : (maximalIdeal R).spanFinrank ≤ 2 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans_le hdim
  have hcases : (maximalIdeal R).spanFinrank ≤ 1 ∨
      (maximalIdeal R).spanFinrank = 2 := by omega
  rcases hcases with hsmall | htwo
  · have hPne : P ≠ ⊥ := P.ne_bot_of_height_eq_one hheight
    have hmne : maximalIdeal R ≠ ⊥ := by
      intro hm
      apply hPne
      exact bot_unique ((le_maximalIdeal (show P.IsPrime from inferInstance).ne_top).trans_eq hm)
    have hrank0 : (maximalIdeal R).spanFinrank ≠ 0 := by
      intro hzero
      exact hmne ((Submodule.spanFinrank_eq_zero_iff_eq_bot
        (IsNoetherian.noetherian (maximalIdeal R))).mp hzero)
    have hrank1 : (maximalIdeal R).spanFinrank = 1 := by omega
    have hmprincipal : (maximalIdeal R).IsPrincipal :=
      ((maximalIdeal R).spanFinrank_eq_one_iff.mp hrank1).1
    have hdim1 : ringKrullDim R ≤ 1 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)]
      exact_mod_cast hsmall
    letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simpa using hdim1)
    have hPm : P = maximalIdeal R :=
      eq_maximalIdeal (Ideal.isMaximal_of_isPrime_of_ne_bot P hPne)
    exact hPm.symm ▸ hmprincipal
  · have hdim2 : ringKrullDim R = 2 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), htwo]
      norm_num
    obtain ⟨x, y, hx, hy, hspan, hxP, hprime, hynot⟩ :=
      regularLocal_dimension_two_exists_parameter_pair_avoiding_heightOnePrime hdim2 P hheight
    exact localPrimeIdeal_isPrincipal_of_pair_parameter_quotient
      P x y hx hy hspan hxP hprime hynot

/-- On the SAME actual smooth cubic chart, every height-one prime has a
regular principal localized equation at EVERY specialization on the curve.
It includes closed surface points and needs no local factoriality assumption.
All maps are the native chart localization maps over the original K. -/
theorem smoothCubic_chartHeightOnePrime_localized_regularPrincipal
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    (P Q : Ideal (ChartRing (equationIdeal p hp) j)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q) (hheight : P.height = 1) :
    ∃ z : Localization.AtPrime Q,
      IsRegular z ∧ P.map (algebraMap (ChartRing (equationIdeal p hp) j)
        (Localization.AtPrime Q)) = Ideal.span ({z} : Set (Localization.AtPrime Q)) := by
  let A := ChartRing (equationIdeal p hp) j
  let S := Localization.AtPrime Q
  letI : IsDomain A := PfaffianDescent.smoothCubic_chartRing_isDomain p hp hp0 j
  letI : IsRegularLocalRing S := PfaffianDescent.smoothCubic_chartLocal_isRegularLocalRing p hp j Q
  have hdisj : Disjoint (Q.primeCompl : Set A) (P : Set A) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    exact hx (hPQ hy)
  letI : (P.map (algebraMap A S)).IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime Q hPQ
  have hlocalHeight : (P.map (algebraMap A S)).height = 1 :=
    (IsLocalization.height_map_of_disjoint Q.primeCompl P hdisj).trans hheight
  have hprincipal := regularLocal_heightOnePrime_isPrincipal_of_dimension_le_two
    (PfaffianDescent.smoothCubic_chartLocal_ringKrullDim_le_two p hp hp0 j Q)
    (P.map (algebraMap A S)) hlocalHeight
  exact PfaffianDescent.heightOnePrime_localized_regularPrincipal_of_localPrincipal
    P Q hPQ hheight hprincipal

end PfaffianDescent.Coray
