import PfaffianDescent.CorayOriginalGenericFullJetDerivation
import PfaffianDescent.CorayOriginalBasisRatioFieldFiniteSeparable
import PfaffianDescent.CorayAiOriginalRatioFieldExactChartSquare
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi

/-! The literal SAMEE coordinate tuple produces a nonzero native generic
2x2 derivative minor in the Etrdeg2 branch. No rank/minor/open outcome is
supplied. Every field action and actual tuple is retained. SOURCE ONLY / HELD. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module KaehlerDifferential
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Differentials of an actual field-generating family span Ω[E/K].
Field-adjoin induction proves this for all actual rational expressions,
including inverse denominators. No differential-spanning premise. -/
theorem fieldGeneratingCoordinates_kaehler_span_eq_top
    {K E : Type u} {ι : Type v} [Field K] [Field E] [Algebra K E]
    (x : ι → E) (hgen : IntermediateField.adjoin K (Set.range x) = ⊤) :
    Submodule.span E (Set.range (fun i => KaehlerDifferential.D K E (x i))) = ⊤ := by
  let S := Submodule.span E (Set.range (fun i => KaehlerDifferential.D K E (x i)))
  have hD : ∀ z : E, KaehlerDifferential.D K E z ∈ S := by
    intro z
    have hz : z ∈ IntermediateField.adjoin K (Set.range x) := by rw [hgen]; trivial
    refine IntermediateField.adjoin_induction K (p := fun z _ => KaehlerDifferential.D K E z ∈ S)
      ?_ ?_ ?_ ?_ ?_ hz
    · rintro z ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self i)
    · intro c
      rw [Derivation.map_algebraMap]
      exact S.zero_mem
    · intro a b ha hb hDa hDb
      rw [map_add]
      exact S.add_mem hDa hDb
    · intro a ha hDa
      rw [Derivation.leibniz_inv]
      exact S.smul_mem _ hDa
    · intro a b ha hb hDa hDb
      rw [Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hDb) (S.smul_mem _ hDa)
  have hle : Submodule.span E (Set.range (KaehlerDifferential.D K E)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro z ⟨a, rfl⟩
    exact hD a
  rw [KaehlerDifferential.span_range_derivation] at hle
  exact top_unique hle

/-- A separable field extension carries the actual generating coordinate
differentials onto Ω[F/K]. The tensor differential surjectivity is derived
from formal étaleness and the finite family is kept literally. -/
theorem fieldGeneratingCoordinates_relativeDifferential_span_eq_top
    {K E F : Type u} {ι : Type v} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra.FormallyEtale E F]
    (x : ι → E) (hgen : IntermediateField.adjoin K (Set.range x) = ⊤) :
    Submodule.span F (Set.range (fun i =>
      KaehlerDifferential.D K F (algebraMap E F (x i)))) = ⊤ := by
  let S := Submodule.span F (Set.range (fun i =>
    KaehlerDifferential.D K F (algebraMap E F (x i))))
  have hmap : ∀ w : KaehlerDifferential K E,
      KaehlerDifferential.map K K E F w ∈ S := by
    intro w
    have hw : w ∈ Submodule.span E
        (Set.range (fun i => KaehlerDifferential.D K E (x i))) := by
      rw [fieldGeneratingCoordinates_kaehler_span_eq_top x hgen]
      trivial
    refine Submodule.span_induction
      (p := fun w _ => KaehlerDifferential.map K K E F w ∈ S) ?_ ?_ ?_ ?_ hw
    · rintro y ⟨i, rfl⟩
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span (Set.mem_range_self i)
    · simpa only [map_zero] using S.zero_mem
    · intro a b ha hb hma hmb
      rw [map_add]
      exact S.add_mem hma hmb
    · intro c y hy hmy
      rw [map_smul]
      exact (S.restrictScalars E).smul_mem c hmy
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange K E F) := by
    intro w
    obtain ⟨t, ht⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K E F).surjective w
    refine ⟨t, ?_⟩
    simpa only [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply] using ht
  apply top_unique
  intro w hw
  obtain ⟨t, rfl⟩ := hsurj w
  clear hw
  induction t with
  | zero => simpa only [map_zero] using S.zero_mem
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
  | tmul a b => rw [KaehlerDifferential.mapBaseChange_tmul]; exact S.smul_mem a (hmap b)

/-- A family spanning the actual two-dimensional coordinate space has
an actual nonzero2x2 minor. The annihilating coordinate functional proves
this directly, without a rank or determinant premise. -/
theorem spanningTwoCoordinateFamily_exists_nonzero_minor
    {F : Type u} {ι : Type v} [Field F] (w : ι → Fin 2 → F)
    (hspan : Submodule.span F (Set.range w) = ⊤) :
    ∃ i j : ι, w i 0 * w j 1 - w i 1 * w j 0 ≠ 0 := by
  classical
  by_contra! hall
  have hz : ∀ i, w i = 0 := by
    intro i
    let ell : (Fin 2 → F) →ₗ[F] F :=
      w i 0 • LinearMap.proj 1 - w i 1 • LinearMap.proj 0
    have hker : Submodule.span F (Set.range w) ≤ LinearMap.ker ell := by
      apply Submodule.span_le.mpr
      rintro v ⟨j, rfl⟩
      change w i 0 * w j 1 - w i 1 * w j 0 = 0
      exact hall i j
    rw [hspan] at hker
    have hi0 : w i 0 = 0 := by
      have h := hker (show (Pi.single (1 : Fin 2) (1 : F)) ∈ (⊤ : Submodule F (Fin 2 → F)) from trivial)
      change ell (Pi.single (1 : Fin 2) (1 : F)) = 0 at h
      simpa [ell, Pi.single_apply] using h
    have hi1 : w i 1 = 0 := by
      have h := hker (show (Pi.single (0 : Fin 2) (1 : F)) ∈ (⊤ : Submodule F (Fin 2 → F)) from trivial)
      change ell (Pi.single (0 : Fin 2) (1 : F)) = 0 at h
      have hn : -w i 1 = 0 := by simpa [ell, Pi.single_apply] using h
      exact neg_eq_zero.mp hn
    funext t
    fin_cases t
    · exact hi0
    · exact hi1
  have hbot : Submodule.span F (Set.range w) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact hz i
  rw [hspan] at hbot
  exact top_ne_bot (le_antisymm hbot bot_le)

/-- ORIGINAL smoothness constructs the native generic pivot derivation;
the SAME E coordinate tuple generates E internally; original F/E
separability then constructs an actual nonzero native normalized-ratio
2x2 derivative minor. No Jacobian/minor/good-open certificate supplied. -/
theorem cubicThroughPointOriginalBasisRatioField_exists_nativeGeneric_minor_of_trdeg_two001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
    let xE := cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a
    let g := @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    Algebra.trdeg K E = 2 →
    ∃ pivot : Fin 3,
      MvPolynomial.aeval z (pderiv (j.succAbove pivot) (p.map (algebraMap K F))) ≠ 0 ∧
      ∃ d : Derivation K F (Fin 2 → F),
      Function.Bijective d.liftKaehlerDifferential ∧
      (∀ i : Fin 4, d (z i) = PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i) ∧
      ∃ i k : Fin m,
        d (E.val (xE i)) 0 * d (E.val (xE k)) 1 -
          d (E.val (xE i)) 1 * d (E.val (xE k)) 0 ≠ 0 := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
  let xE := cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a
  let g := @affineChartGenericEvaluation
    (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  change Algebra.trdeg K E = 2 →
    ∃ pivot : Fin 3,
      MvPolynomial.aeval z (pderiv (j.succAbove pivot) (p.map (algebraMap K F))) ≠ 0 ∧
      ∃ d : Derivation K F (Fin 2 → F),
        Function.Bijective d.liftKaehlerDifferential ∧
        (∀ i : Fin 4, d (z i) = PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i) ∧
        ∃ i k : Fin m,
          d (E.val (xE i)) 0 * d (E.val (xE k)) 1 -
            d (E.val (xE i)) 1 * d (E.val (xE k)) 0 ≠ 0
  intro hE
  letI : Algebra.IsSeparable E F :=
    (cubicThroughPointOriginalBasisRatioField_finite_separable_of_trdeg_two p hp hp0 n y hpy j b a hE).2
  letI : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F
  obtain ⟨pivot, hgrad, d, hbij, hd⟩ := smoothOriginalCubic_generic_exists_nativeDerivationKaehlerIso001 p hp hp0 j
  have hgen : IntermediateField.adjoin K (Set.range xE) = ⊤ :=
    cubicThroughPointOriginalBasisRatioFieldCoordinates_adjoin_eq_top001 p hp n y hpy j b a
  have hspan := fieldGeneratingCoordinates_relativeDifferential_span_eq_top (F := F) xE hgen
  have hm := congrArg (Submodule.map d.liftKaehlerDifferential) hspan
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hbij.2, ← Set.range_comp'] at hm
  have hfamily :
      (fun i => d.liftKaehlerDifferential (KaehlerDifferential.D K F (algebraMap E F (xE i)))) =
        (fun i => d (E.val (xE i))) := by
    funext i
    change d.liftKaehlerDifferential (KaehlerDifferential.D K F (E.val (xE i))) = d (E.val (xE i))
    exact d.liftKaehlerDifferential_comp_D (E.val (xE i))
  have hnativeSpan : Submodule.span F (Set.range (fun i => d (E.val (xE i)))) = ⊤ := by
    change Submodule.span F (Set.range (fun i =>
      d.liftKaehlerDifferential (KaehlerDifferential.D K F (algebraMap E F (xE i))))) = ⊤ at hm
    rw [hfamily] at hm
    exact hm
  obtain ⟨i, k, hminor⟩ := spanningTwoCoordinateFamily_exists_nonzero_minor
    (fun i => d (E.val (xE i))) hnativeSpan
  exact ⟨pivot, hgrad, d, hbij, hd, i, k, hminor⟩

end PfaffianDescent.Coray
end
