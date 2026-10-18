import PfaffianDescent.OriginalArtinSupportHilbertBurch318
import PfaffianDescent.SemilocalMatrixPrincipalPresentation
import PfaffianDescent.ActualArtinianQuotientLocalizationIso

/-!
Construct a single principal neighborhood of the entire original finite-flat
family and its actual cofactor presentation. Residual regularity is assumed
only at the actual tensor-residue support; no semilocal data is an input.
The empty family is treated internally by the zero-column presentation.
-/

noncomputable section
namespace PfaffianDescent
open Matrix LinearMap
open AllCharacteristics.HilbertSurfaceDraft
universe u

theorem zeroColumn_hilbertBurch_cofactor318
    {R : Type u} [CommRing R]
    (M : Matrix (Option (Fin 0)) (Fin 0) R) (i : Option (Fin 0)) :
    hilbertBurchCofactors318 M i = 1 := by
  cases i with
  | none =>
    change (hilbertBurchAugment318 M).adjugate none none = 1
    rw [Matrix.adjugate_eq_one_of_card_eq_one (by simp)]
    rfl
  | some j => exact Fin.elim0 j

theorem zeroColumn_hilbertBurch_cofactorIdeal_eq_top318
    {R : Type u} [CommRing R]
    (M : Matrix (Option (Fin 0)) (Fin 0) R) :
    Ideal.span (Set.range (hilbertBurchCofactors318 M)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← zeroColumn_hilbertBurch_cofactor318 M none]
  exact Ideal.mem_span_range_self (x := none)

theorem zeroColumn_hilbertBurch_exact318
    {R : Type u} [CommRing R]
    (M : Matrix (Option (Fin 0)) (Fin 0) R) :
    Function.Exact M.mulVecLin (rowFunctional008 (hilbertBurchCofactors318 M)) := by
  apply LinearMap.exact_iff.mpr
  ext x
  constructor
  · intro hx
    have hxrow : rowFunctional008 (hilbertBurchCofactors318 M) x = 0 := hx
    have hxnone : x none = 0 := by
      have hxdefault : x (default : Option (Fin 0)) = 0 := by
        simpa [rowFunctional008_apply, dotProduct,
          zeroColumn_hilbertBurch_cofactor318] using hxrow
      exact (congrArg x (Subsingleton.elim (none : Option (Fin 0)) default)).trans hxdefault
    have hxzero : x = 0 := by
      ext i
      cases i with
      | none => exact hxnone
      | some j => exact Fin.elim0 j
    refine ⟨0, ?_⟩
    rw [hxzero]
    exact map_zero _
  · rintro ⟨v, rfl⟩
    exact hilbertBurchCofactors_mulVec_zero001 M v

/-- Construct the actual original principal denominator and coefficient
matrix. The denominator avoids the whole family, and every further
principal shrinking retains the whole-ideal cofactor equality and exact
cofactor complex. No nonempty-family assumption is needed. -/
theorem exists_originalArtinSupport_principal_hilbertBurch318
    (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S] [Algebra.FiniteType S A]
    [Module.Flat S A] (J : Ideal A)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)]
    (hreg : ∀ Q ∈ originalArtinResidueSupport318 S A J,
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal))
    (hdim : ∀ Q ∈ originalArtinResidueSupport318 S A J,
      ringKrullDim (Localization.AtPrime Q.asIdeal) = 2) :
    ∃ (m : ℕ) (r : A) (N : Matrix (Option (Fin m)) (Fin m) A),
      r ∈ finiteSupportDenominators001 (originalArtinSupport318 S A J) ∧
      ∀ s : A, r ∣ s →
        J.map (algebraMap A (Localization.Away s)) =
          Ideal.span (Set.range (hilbertBurchCofactors318
            (N.map (algebraMap A (Localization.Away s))))) ∧
        Function.Exact (N.map (algebraMap A (Localization.Away s))).mulVecLin
          (rowFunctional008 (hilbertBurchCofactors318
            (N.map (algebraMap A (Localization.Away s))))) := by
  classical
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  by_cases hJ : J = ⊤
  · let N : Matrix (Option (Fin 0)) (Fin 0) A := 0
    refine ⟨0, 1, N, Submonoid.one_mem _, fun s _ => ?_⟩
    constructor
    · rw [hJ, Ideal.map_top]
      exact (zeroColumn_hilbertBurch_cofactorIdeal_eq_top318 _).symm
    · exact zeroColumn_hilbertBurch_exact318 _
  · letI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    obtain ⟨m, M, _, hJcof, hMrange⟩ :=
      exists_originalArtinSupport_hilbertBurch_resolution318 S A J hreg hdim
    have hex : Function.Exact M.mulVecLin
        (rowFunctional008 (hilbertBurchCofactors318 M)) :=
      LinearMap.exact_iff.mpr hMrange.symm
    obtain ⟨r, N, hr, hspread⟩ :=
      semilocalMatrix_exists_principal_cofactorPresentation001
        (finiteSupportDenominators001 (originalArtinSupport318 S A J)) J M hJcof hex
    exact ⟨m, r, N, hr, hspread⟩

/-- Specialize the constructed neighborhood to its actual denominator.
Its nonvanishing on the entire family is expressed by an actual unit in
the original quotient algebra, not a reduced-support assertion. -/
theorem exists_originalArtin_wholeFamily_principal_hilbertBurch318
    (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S] [Algebra.FiniteType S A]
    [Module.Flat S A] (J : Ideal A)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)]
    (hreg : ∀ Q ∈ originalArtinResidueSupport318 S A J,
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal))
    (hdim : ∀ Q ∈ originalArtinResidueSupport318 S A J,
      ringKrullDim (Localization.AtPrime Q.asIdeal) = 2) :
    ∃ (m : ℕ) (r : A) (N : Matrix (Option (Fin m)) (Fin m) A),
      r ∈ finiteSupportDenominators001 (originalArtinSupport318 S A J) ∧
      IsUnit (Ideal.Quotient.mk J r) ∧
      J.map (algebraMap A (Localization.Away r)) =
        Ideal.span (Set.range (hilbertBurchCofactors318
          (N.map (algebraMap A (Localization.Away r))))) ∧
      Function.Exact (N.map (algebraMap A (Localization.Away r))).mulVecLin
        (rowFunctional008 (hilbertBurchCofactors318
          (N.map (algebraMap A (Localization.Away r))))) := by
  letI : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite S _
  obtain ⟨m, r, N, hr, hspread⟩ :=
    exists_originalArtinSupport_principal_hilbertBurch318 S A J hreg hdim
  have hractual : r ∈ finiteSupportDenominators001 (actualArtinianQuotientSupport001 J) := hr
  obtain ⟨hJcof, hex⟩ := hspread r dvd_rfl
  exact ⟨m, r, N, hr, actualArtinianQuotientSupport_denominator_isUnit001 J r hractual,
    hJcof, hex⟩

end PfaffianDescent
end
